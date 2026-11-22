#!/usr/bin/env python3
"""
Machina - CAD De-ID Pipeline
Processes ./input into <attempt_dir>/corpus while keeping temporary state
and private entity mappings in a separate --work-dir outside the submission tree.
"""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import os
import re
import shutil
import tarfile
import tempfile
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Set, Tuple

# Optional third-party libraries (graceful fallback if unavailable)
try:
    from pypdf import PdfReader, PdfWriter  # type: ignore
except Exception:  # pragma: no cover
    PdfReader = None
    PdfWriter = None

try:
    import pikepdf  # type: ignore
except Exception:  # pragma: no cover
    pikepdf = None

try:
    import olefile  # type: ignore
except Exception:  # pragma: no cover
    olefile = None

try:
    from PIL import Image  # type: ignore
except Exception:  # pragma: no cover
    Image = None


TEXT_EXTENSIONS = {
    ".txt", ".md", ".rst", ".csv", ".tsv", ".json", ".jsonl", ".xml", ".yml",
    ".yaml", ".toml", ".ini", ".cfg", ".conf", ".log", ".step", ".stp",
    ".iges", ".igs", ".dxf", ".nc", ".tap", ".gcode", ".bom", ".mtl", ".obj",
    ".svg", ".html", ".htm", ".py", ".c", ".h", ".cpp", ".hpp", ".js", ".ts",
    ".sh", ".ps1", ".bat", ".sql", ".props", ".csproj", ".vcxproj"
}

ARCHIVE_EXTENSIONS = {".zip", ".tar", ".tgz", ".tar.gz", ".tbz2", ".tar.bz2", ".txz", ".tar.xz"}

PDF_EXTENSIONS = {".pdf"}

IMAGE_EXTENSIONS = {".png", ".jpg", ".jpeg", ".tif", ".tiff", ".bmp", ".webp"}

NATIVE_CAD_EXTENSIONS = {
    ".sldprt", ".sldasm", ".slddrw",  # SolidWorks
    ".ipt", ".iam", ".idw", ".ipn",     # Autodesk Inventor
    ".prt", ".asm", ".drw", ".catpart", ".catproduct", ".f3d", ".x_t", ".x_b", ".sat"
}

# Common identifier patterns (emails, URLs/domains, phones, handles, part/project codes)
EMAIL_RE = re.compile(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b")
URL_RE = re.compile(r"\bhttps?://[^\s<>\"')]+", re.IGNORECASE)
PHONE_RE = re.compile(r"(?<!\w)(?:\+?\d{1,3}[\s.-]?)?(?:\(?\d{3}\)?[\s.-]?)\d{3}[\s.-]?\d{4}(?!\w)")
# Matches explicit labeled metadata fields like Author: Jane Doe, Company: Acme Corp, Project: PRJ-1042
LABELED_ID_RE = re.compile(
    r"(?im)^([ \t]*(?:author|creator|owner|company|organization|org|customer|client|"
    r"vendor|supplier|contractor|project|program|drawn[_\s-]?by|checked[_\s-]?by|"
    r"approved[_\s-]?by|email|e-mail|phone|tel|address|site|location)[ \t]*[:=][ \t]*)([^\r\n]+)$"
)
# Token matcher for discovered/candidate identifiers (alphanumeric + _ - . with letters/digits)
TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9._-]{2,63}")


def get_compound_ext(name: str) -> str:
    lower = name.lower()
    for ext in (".tar.gz", ".tar.bz2", ".tar.xz"):
        if lower.endswith(ext):
            return ext
    return Path(name).suffix.lower()


def is_archive(path: Path) -> bool:
    return get_compound_ext(path.name) in ARCHIVE_EXTENSIONS


class Pseudonymizer:
    """
    Deterministic, collision-free pseudonym registry keyed by canonical normalized value.
    Never writes the raw mapping to the submission folder unless explicitly saved to --work-dir.
    """

    def __init__(self, salt: str, seed_terms: Optional[Iterable[str]] = None) -> None:
        self.salt = salt.encode("utf-8")
        self._to_pseudo: Dict[str, str] = {}
        self._used_pseudos: Set[str] = set()
        self._counters: Dict[str, int] = {}
        if seed_terms:
            for term in seed_terms:
                cleaned = term.strip()
                if cleaned:
                    self.register(cleaned, category="ENTITY")

    def _digest_hex(self, kind: str, raw_val: str) -> str:
        mac = hmac.new(self.salt, f"{kind}:{raw_val}".encode("utf-8"), hashlib.sha256).hexdigest()
        return mac[:8].upper()

    def register(self, raw_val: str, category: str = "ENTITY") -> str:
        val = raw_val.strip()
        if not val:
            return raw_val
        key = f"{category}:{val.casefold()}"
        if key in self._to_pseudo:
            return self._to_pseudo[key]

        base_code = self._digest_hex(category, val.casefold())
        prefix_map = {
            "PERSON": "ENG",
            "COMPANY": "ORG",
            "PROJECT": "PRJ",
            "PART": "PRT",
            "EMAIL": "contact",
            "DOMAIN": "example-org.invalid",
            "PHONE": "555-0100",
            "ADDRESS": "100-PSEUDO-WAY",
            "PATH": "seg",
            "ENTITY": "ENT",
        }
        prefix = prefix_map.get(category, "ID")

        if category == "DOMAIN":
            candidate = f"{base_code.lower()}.example.invalid"
        elif category == "EMAIL":
            candidate = f"user_{base_code.lower()}@example.invalid"
        elif category == "PHONE":
            n = self._counters.setdefault("PHONE", 100)
            self._counters["PHONE"] += 1
            candidate = f"+1-555-019-{n:04d}"
        else:
            candidate = f"{prefix}-{base_code}"

        # Guarantee distinct pseudonyms for distinct identities even on hash prefix collision
        bump = 1
        while candidate in self._used_pseudos:
            candidate = f"{candidate}-{bump}"
            bump += 1

        self._to_pseudo[key] = candidate
        self._used_pseudos.add(candidate)
        return candidate

    def get_if_known(self, token: str) -> Optional[str]:
        if not token:
            return None
        # Exact match first, then casefolded match across categories
        for cat in ("PERSON", "COMPANY", "PROJECT", "PART", "EMAIL", "DOMAIN", "PHONE", "ADDRESS", "PATH", "ENTITY"):
            val = self._to_pseudo.get(f"{cat}:{token.casefold()}")
            if val:
                return val
        return None


@dataclass
class DefectReport:
    empty_files: List[str] = field(default_factory=list)
    corrupt_or_unreadable: List[Tuple[str, str]] = field(default_factory=list)
    skipped_large_or_symlink: List[Tuple[str, str]] = field(default_factory=list)
    processed_count: int = 0


def sanitize_text_blob(text: str, pseudo: Pseudonymizer) -> str:
    """Replaces known identifiers, emails, URLs, phones, and labeled metadata values."""
    if not text:
        return text

    # 1. Emails -> deterministic pseudo email
    def _sub_email(m: re.Match) -> str:
        return pseudo.register(m.group(0), "EMAIL")

    text = EMAIL_RE.sub(_sub_email, text)

    # 2. URLs -> preserve scheme, replace domain/path segments deterministically
    def _sub_url(m: re.Match) -> str:
        url = m.group(0)
        m_parts = re.match(r"^(https?://)([^/:?#\s]+)(.*)$", url, re.IGNORECASE)
        if not m_parts:
            return url
        scheme, host, rest = m_parts.groups()
        p_host = pseudo.register(host, "DOMAIN")
        return f"{scheme}{p_host}{rest}"

    text = URL_RE.sub(_sub_url, text)

    # 3. Phone numbers
    def _sub_phone(m: re.Match) -> str:
        digits_only = re.sub(r"\D", "", m.group(0))
        if len(digits_only) < 7:
            return m.group(0)
        return pseudo.register(m.group(0), "PHONE")

    text = PHONE_RE.sub(_sub_phone, text)

    # 4. Labeled metadata lines (e.g. Author: ..., Company: ..., Project: ...)
    def _sub_labeled(m: re.Match) -> str:
        prefix, val = m.group(1), m.group(2).strip()
        lower_p = prefix.lower()
        if any(k in lower_p for k in ("company", "organization", "org", "customer", "client", "vendor", "supplier", "contractor")):
            cat = "COMPANY"
        elif any(k in lower_p for k in ("project", "program")):
            cat = "PROJECT"
        elif "address" in lower_p or "site" in lower_p or "location" in lower_p:
            cat = "ADDRESS"
        else:
            cat = "PERSON"
        return f"{prefix}{pseudo.register(val, cat)}"

    text = LABELED_ID_RE.sub(_sub_labeled, text)

    # 5. Any previously registered or seeded identifier tokens
    def _sub_known(m: re.Match) -> str:
        tok = m.group(0)
        mapped = pseudo.get_if_known(tok)
        return mapped if mapped else tok

    text = TOKEN_RE.sub(_sub_known, text)
    return text


def sanitize_rel_path(rel_path: Path, pseudo: Pseudonymizer) -> Path:
    """
    De-identifies path components (folder names and file stems) while preserving
    every file extension and keeping directory hierarchy aligned.
    """
    parts = list(rel_path.parts)
    if not parts:
        return rel_path

    new_parts: List[str] = []
    for idx, part in enumerate(parts):
        is_last = idx == len(parts) - 1
        if not is_last:
            # Folder name: replace known entities or obvious custom org/project segments
            mapped = pseudo.get_if_known(part)
            if mapped:
                new_parts.append(mapped)
            else:
                new_parts.append(sanitize_text_blob(part, pseudo))
        else:
            ext = get_compound_ext(part)
            stem = part[: len(part) - len(ext)] if ext else part
            mapped_stem = pseudo.get_if_known(stem)
            if mapped_stem:
                new_stem = mapped_stem
            else:
                new_stem = sanitize_text_blob(stem, pseudo)
            new_parts.append(f"{new_stem}{ext}")

    return Path(*new_parts)


def process_pdf(src: Path, dst: Path, pseudo: Pseudonymizer, report: DefectReport, rel_label: str) -> None:
    """De-identifies PDF metadata and preserves page content & structure."""
    dst.parent.mkdir(parents=True, exist_ok=True)
    if pikepdf is not None:
        try:
            with pikepdf.open(src, allow_overwriting_input=True) as pdf:
                with pdf.open_metadata() as meta:
                    for key in list(meta.keys()):
                        val = str(meta[key])
                        if val:
                            meta[key] = sanitize_text_blob(val, pseudo)
                for k, v in list(pdf.docinfo.items()):
                    pdf.docinfo[k] = pikepdf.String(sanitize_text_blob(str(v), pseudo))
                pdf.save(dst)
            return
        except Exception as exc:
            report.corrupt_or_unreadable.append((rel_label, f"pikepdf fallback: {exc}"))

    if PdfReader is not None and PdfWriter is not None:
        try:
            reader = PdfReader(str(src))
            writer = PdfWriter()
            for page in reader.pages:
                writer.add_page(page)
            if reader.metadata:
                clean_meta = {}
                for k, v in reader.metadata.items():
                    if isinstance(v, str):
                        clean_meta[k] = sanitize_text_blob(v, pseudo)
                writer.add_metadata(clean_meta)
            with dst.open("wb") as f_out:
                writer.write(f_out)
            return
        except Exception as exc:
            report.corrupt_or_unreadable.append((rel_label, f"pypdf fallback: {exc}"))

    shutil.copy2(src, dst)


def process_image(src: Path, dst: Path, pseudo: Pseudonymizer, report: DefectReport, rel_label: str) -> None:
    """Strips/sanitizes image EXIF/PNG metadata while preserving pixel data and format."""
    dst.parent.mkdir(parents=True, exist_ok=True)
    if Image is not None:
        try:
            with Image.open(src) as im:
                # Preserve mode/format and strip identifying EXIF/info tags safely
                info = {}
                for k, v in (im.info or {}).items():
                    if isinstance(v, str):
                        info[k] = sanitize_text_blob(v, pseudo)
                fmt = im.format or src.suffix.lstrip(".").upper()
                if fmt == "JPG":
                    fmt = "JPEG"
                save_kwargs = {}
                if fmt in {"PNG", "WEBP", "TIFF"}:
                    pass
                im.save(dst, format=fmt if fmt in {"PNG", "JPEG", "WEBP", "TIFF", "BMP", "GIF"} else None, **save_kwargs)
                return
        except Exception as exc:
            report.corrupt_or_unreadable.append((rel_label, f"image preserved raw: {exc}"))
    shutil.copy2(src, dst)


def rewrite_ascii_occurrences_in_bytes(data: bytearray, pseudo: Pseudonymizer) -> bytearray:
    """
    Safely rewrites ASCII tokens in mixed/binary/CAD files ONLY when the replacement
    has the exact same byte length (preserving fixed-offset binary/CAD tables and geometry),
    or updates plain-text lines cleanly.
    """
    # For pure UTF-8 text files, caller uses sanitize_text_blob directly.
    # For binary/CAD files, replace exact byte matches of equal length so offsets never shift.
    for cat in ("PERSON", "COMPANY", "PROJECT", "PART", "EMAIL", "DOMAIN", "PHONE", "ADDRESS", "ENTITY"):
        for k, p_val in list(pseudo._to_pseudo.items()):
            if not k.startswith(f"{cat}:"):
                continue
            orig_raw = k.split(":", 1)[1].encode("utf-8", errors="ignore")
            p_bytes = p_val.encode("utf-8", errors="ignore")
            if orig_raw and len(orig_raw) == len(p_bytes):
                start = 0
                while True:
                    pos = data.find(orig_raw, start)
                    if pos == -1:
                        break
                    data[pos : pos + len(p_bytes)] = p_bytes
                    start = pos + len(p_bytes)
    return data


def process_single_file(
    src: Path,
    dst_root: Path,
    rel_path: Path,
    pseudo: Pseudonymizer,
    report: DefectReport,
    tmp_root: Path,
) -> None:
    rel_label = rel_path.as_posix()

    if src.is_symlink():
        report.skipped_large_or_symlink.append((rel_label, "symlink skipped"))
        return

    try:
        st = src.stat()
    except OSError as exc:
        report.corrupt_or_unreadable.append((rel_label, f"stat failed: {exc}"))
        return

    if st.st_size == 0:
        report.empty_files.append(rel_label)
        out_path = dst_root / sanitize_rel_path(rel_path, pseudo)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.touch()
        report.processed_count += 1
        return

    out_rel = sanitize_rel_path(rel_path, pseudo)
    out_path = dst_root / out_rel
    out_path.parent.mkdir(parents=True, exist_ok=True)

    ext = get_compound_ext(src.name)

    if ext in PDF_EXTENSIONS:
        process_pdf(src, out_path, pseudo, report, rel_label)
        report.processed_count += 1
        return

    if ext in IMAGE_EXTENSIONS:
        process_image(src, out_path, pseudo, report, rel_label)
        report.processed_count += 1
        return

    if is_archive(src):
        process_archive(src, out_path, pseudo, report, tmp_root, rel_label)
        report.processed_count += 1
        return

    # Text / STEP / IGES / DXF / JSON / XML / CSV / BOM / etc.
    if ext in TEXT_EXTENSIONS:
        try:
            raw_bytes = src.read_bytes()
            text = raw_bytes.decode("utf-8")
            cleaned = sanitize_text_blob(text, pseudo)
            out_path.write_text(cleaned, encoding="utf-8")
            report.processed_count += 1
            return
        except UnicodeDecodeError:
            # Fall through to safe binary/CAD handling
            pass
        except Exception as exc:
            report.corrupt_or_unreadable.append((rel_label, f"text read/write error: {exc}"))
            shutil.copy2(src, out_path)
            report.processed_count += 1
            return

    # Native CAD or other binary format: do not corrupt binary headers/geometry;
    # perform equal-length byte substitution for known identifiers and copy intact.
    try:
        data = bytearray(src.read_bytes())
        cleaned_data = rewrite_ascii_occurrences_in_bytes(data, pseudo)
        out_path.write_bytes(bytes(cleaned_data))
        report.processed_count += 1
    except Exception as exc:
        report.corrupt_or_unreadable.append((rel_label, f"binary copy fallback: {exc}"))
        shutil.copy2(src, out_path)
        report.processed_count += 1


def process_archive(
    src: Path,
    dst_archive: Path,
    pseudo: Pseudonymizer,
    report: DefectReport,
    tmp_root: Path,
    rel_label: str,
) -> None:
    """
    Unpacks an archive into a temporary directory, recursively de-identifies all
    entries and filenames (including nested archives), and repackages cleanly
    so no raw/unprocessed original identifiers remain inside the output archive.
    """
    extract_dir = Path(tempfile.mkdtemp(prefix="arc_in_", dir=str(tmp_root)))
    clean_dir = Path(tempfile.mkdtemp(prefix="arc_out_", dir=str(tmp_root)))
    try:
        lower = src.name.lower()
        if lower.endswith(".zip"):
            with zipfile.ZipFile(src, "r") as zf:
                for member in zf.infolist():
                    if member.is_dir():
                        continue
                    target = (extract_dir / member.filename).resolve()
                    if not str(target).startswith(str(extract_dir.resolve())):
                        continue
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with zf.open(member, "r") as r_f, target.open("wb") as w_f:
                        shutil.copyfileobj(r_f, w_f)
        elif any(lower.endswith(s) for s in (".tar", ".tgz", ".tar.gz", ".tbz2", ".tar.bz2", ".txz", ".tar.xz")):
            with tarfile.open(src, "r:*") as tf:
                for member in tf.getmembers():
                    if not member.isfile():
                        continue
                    target = (extract_dir / member.name).resolve()
                    if not str(target).startswith(str(extract_dir.resolve())):
                        continue
                    target.parent.mkdir(parents=True, exist_ok=True)
                    extracted = tf.extractfile(member)
                    if extracted is not None:
                        with extracted, target.open("wb") as w_f:
                            shutil.copyfileobj(extracted, w_f)
        else:
            shutil.copy2(src, dst_archive)
            return

        # Process all unpacked entries recursively
        for root, _dirs, files in os.walk(extract_dir):
            for fname in sorted(files):
                f_path = Path(root) / fname
                entry_rel = f_path.relative_to(extract_dir)
                process_single_file(
                    f_path,
                    clean_dir,
                    entry_rel,
                    pseudo,
                    report,
                    tmp_root,
                    f"{rel_label}!{entry_rel.as_posix()}",
                )

        # Repackage archive
        if lower.endswith(".zip"):
            with zipfile.ZipFile(dst_archive, "w", compression=zipfile.ZIP_DEFLATED) as zf_out:
                for root, _dirs, files in os.walk(clean_dir):
                    for fname in sorted(files):
                        f_path = Path(root) / fname
                        arcname = f_path.relative_to(clean_dir).as_posix()
                        zf_out.write(f_path, arcname=arcname)
        elif lower.endswith(".tar"):
            with tarfile.open(dst_archive, "w") as tf_out:
                for root, _dirs, files in os.walk(clean_dir):
                    for fname in sorted(files):
                        f_path = Path(root) / fname
                        arcname = f_path.relative_to(clean_dir).as_posix()
                        tf_out.add(f_path, arcname=arcname)
        elif lower.endswith(".tgz") or lower.endswith(".tar.gz"):
            with tarfile.open(dst_archive, "w:gz") as tf_out:
                for root, _dirs, files in os.walk(clean_dir):
                    for fname in sorted(files):
                        f_path = Path(root) / fname
                        arcname = f_path.relative_to(clean_dir).as_posix()
                        tf_out.add(f_path, arcname=arcname)
        elif lower.endswith(".tbz2") or lower.endswith(".tar.bz2"):
            with tarfile.open(dst_archive, "w:bz2") as tf_out:
                for root, _dirs, files in os.walk(clean_dir):
                    for fname in sorted(files):
                        f_path = Path(root) / fname
                        arcname = f_path.relative_to(clean_dir).as_posix()
                        tf_out.add(f_path, arcname=arcname)
        elif lower.endswith(".txz") or lower.endswith(".tar.xz"):
            with tarfile.open(dst_archive, "w:xz") as tf_out:
                for root, _dirs, files in os.walk(clean_dir):
                    for fname in sorted(files):
                        f_path = Path(root) / fname
                        arcname = f_path.relative_to(clean_dir).as_posix()
                        tf_out.add(f_path, arcname=arcname)

    except Exception as exc:
        report.corrupt_or_unreadable.append((rel_label, f"archive unpack/repack error: {exc}"))
        shutil.copy2(src, dst_archive)
    finally:
        shutil.rmtree(extract_dir, ignore_errors=True)
        shutil.rmtree(clean_dir, ignore_errors=True)


def discover_input_files(input_dir: Path) -> List[Path]:
    all_files: List[Path] = []
    for root, _dirs, files in os.walk(input_dir):
        for name in sorted(files):
            p = Path(root) / name
            if ".get-input" in p.parts:
                continue
            all_files.append(p.relative_to(input_dir))
    return all_files


def main() -> None:
    parser = argparse.ArgumentParser(description="De-identify Machina CAD corpus into attempt-N/corpus")
    parser.add_argument("--input", type=Path, required=True, help="Path to ./input corpus directory")
    parser.add_argument("--attempt-dir", type=Path, required=True, help="Path to attempt-N directory")
    parser.add_argument("--work-dir", type=Path, required=True, help="Temp & private mapping dir (outside attempt-N)")
    parser.add_argument("--salt", default="machina-deid-v1-salt", help="Deterministic HMAC salt")
    parser.add_argument("--seed-terms-file", type=Path, help="Optional newline-separated identifier list")
    parser.add_argument("--workers", type=int, default=os.cpu_count() or 8, help="Worker thread count")
    args = parser.parse_args()

    input_dir = args.input.resolve()
    attempt_dir = args.attempt_dir.resolve()
    work_dir = args.work_dir.resolve()
    corpus_out = attempt_dir / "corpus"
    tmp_root = work_dir / "tmp"

    corpus_out.mkdir(parents=True, exist_ok=True)
    tmp_root.mkdir(parents=True, exist_ok=True)

    seed_terms: List[str] = []
    if args.seed_terms_file and args.seed_terms_file.is_file():
        seed_terms = [
            line.strip()
            for line in args.seed_terms_file.read_text(encoding="utf-8", errors="ignore").splitlines()
            if line.strip() and not line.strip().startswith("#")
        ]

    pseudo = Pseudonymizer(salt=args.salt, seed_terms=seed_terms)
    report = DefectReport()

    rel_files = discover_input_files(input_dir)
    print(f"Discovered {len(rel_files)} files under {input_dir}", flush=True)

    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as pool:
        futures = {
            pool.submit(
                process_single_file,
                input_dir / rel,
                corpus_out,
                rel,
                pseudo,
                report,
                tmp_root,
                rel.as_posix(),
            ): rel
            for rel in rel_files
        }
        completed = 0
        for fut in as_completed(futures):
            fut.result()
            completed += 1
            if completed % 2500 == 0 or completed == len(rel_files):
                print(f"Processed {completed}/{len(rel_files)} files...", flush=True)

    # Save private summary outside attempt-N so attempt-N stays clean
    summary_path = work_dir / "run_summary.json"
    summary_path.write_text(
        json.dumps(
            {
                "total_discovered": len(rel_files),
                "processed_count": report.processed_count,
                "empty_files_count": len(report.empty_files),
                "corrupt_or_unreadable_count": len(report.corrupt_or_unreadable),
                "skipped_large_or_symlink_count": len(report.skipped_large_or_symlink),
                "empty_files_sample": report.empty_files[:200],
                "corrupt_or_unreadable_sample": report.corrupt_or_unreadable[:200],
                "skipped_large_or_symlink_sample": report.skipped_large_or_symlink[:200],
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    print(f"Done. Output written to {corpus_out} (summary in {summary_path})", flush=True)


if __name__ == "__main__":
    main()