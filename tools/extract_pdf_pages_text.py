#!/usr/bin/env python3
"""Extract selected physical PDF pages into a page-delimited UTF-8 text file."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

from pypdf import PdfReader


def parse_pages(specification: str) -> list[int]:
    pages: set[int] = set()
    for item in specification.split(","):
        item = item.strip()
        if not item:
            continue
        if "-" in item:
            start_text, end_text = item.split("-", maxsplit=1)
            start = int(start_text)
            end = int(end_text)
            if start > end:
                raise ValueError(f"descending page range: {item}")
            pages.update(range(start, end + 1))
        else:
            pages.add(int(item))
    if not pages or min(pages) < 1:
        raise ValueError("pages must be positive, one-based physical page numbers")
    return sorted(pages)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pdf", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--pages",
        required=True,
        help="comma-separated one-based physical pages and ranges, e.g. 11,20,37-38",
    )
    parser.add_argument(
        "--mode",
        choices=("plain", "layout"),
        default="plain",
        help="pypdf extraction mode (plain is searchable; layout preserves placement)",
    )
    args = parser.parse_args()

    pages = parse_pages(args.pages)
    reader = PdfReader(args.pdf, strict=False)
    if pages[-1] > len(reader.pages):
        raise ValueError(
            f"physical page {pages[-1]} exceeds PDF page count {len(reader.pages)}"
        )

    lines = [
        f"SOURCE: {args.pdf.resolve()}",
        f"SOURCE_SHA256: {sha256(args.pdf)}",
        f"PDF_PHYSICAL_PAGE_COUNT: {len(reader.pages)}",
        f"EXTRACTED_PHYSICAL_PAGES: {','.join(map(str, pages))}",
        f"EXTRACTION_MODE: pypdf {args.mode}",
        "NOTE: Machine extraction is an index, not an authoritative formula transcription.",
        "",
    ]
    for physical_page in pages:
        lines.append(f"===== PDF PHYSICAL PAGE {physical_page} =====")
        text = (
            reader.pages[physical_page - 1].extract_text(extraction_mode=args.mode)
            or ""
        )
        lines.append(text.rstrip())
        lines.append("")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
