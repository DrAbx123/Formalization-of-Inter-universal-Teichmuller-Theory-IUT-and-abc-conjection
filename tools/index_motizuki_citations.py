from __future__ import annotations

import csv
import re
from pathlib import Path

from pypdf import PdfReader


ROOT = Path(__file__).resolve().parents[1] / "papers" / "motizuki_corpus"
RAW = ROOT / "raw"
TEXT = ROOT / "text"
TEXT.mkdir(parents=True, exist_ok=True)

KEYWORDS = [
    "Inter-universal Teichmuller",
    "Inter-universal Teichmüller",
    "Frobenioid",
    "Hodge-Arakelov",
    "etale theta",
    "étale theta",
    "anabelian",
    "Grothendieck conjecture",
    "ABC conjecture",
    "Szpiro",
    "Mason-Stothers",
    "Belyi",
    "Kummer",
    "log scheme",
]

TITLE_ALIASES = {
    "IUT-I": ["Inter-universal Teichmuller Theory I", "IUT I"],
    "IUT-II": ["Inter-universal Teichmuller Theory II", "IUT II"],
    "IUT-III": ["Inter-universal Teichmuller Theory III", "IUT III"],
    "IUT-IV": ["Inter-universal Teichmuller Theory IV", "IUT IV"],
    "PANORAMIC": ["Panoramic Overview of Inter-universal Teichmuller Theory"],
    "ESSENTIAL-LOGIC": ["Essential Logical Structure of Inter-universal Teichmuller Theory"],
    "EXPLICIT-ESTIMATES": ["Explicit estimates in IUTeich"],
}


def clean_line(line: str) -> str:
    return re.sub(r"\s+", " ", line).strip()


def reference_lines(text: str) -> list[str]:
    lines = [clean_line(line) for line in text.splitlines()]
    hits: list[str] = []
    in_refs = False
    for line in lines:
        lower = line.lower()
        if re.search(r"^(references|bibliography|参考文献|文献)$", lower):
            in_refs = True
        if in_refs and line and len(line) >= 8:
            hits.append(line[:1000])
    return hits


def main() -> None:
    manifest = ROOT / "pdfs.csv"
    docs_path = ROOT / "documents.csv"
    edges_path = ROOT / "citation_candidates.tsv"
    keywords_path = ROOT / "keyword_hits.tsv"
    docs: list[dict[str, str]] = []
    edges: list[dict[str, str]] = []
    keyword_hits: list[dict[str, str]] = []

    with manifest.open(encoding="utf-8-sig", newline="") as stream:
        rows = list(csv.DictReader(stream))

    target_texts: dict[str, str] = {}
    for position, row in enumerate(rows, start=1):
        file_name = row["file"]
        path = RAW / file_name
        if not path.exists() or not row.get("sha256"):
            docs.append({
                "file": file_name,
                "url": row.get("url", ""),
                "sha256": row.get("sha256", ""),
                "status": "missing-download",
                "pages": "0",
                "text_chars": "0",
                "text_file": "",
            })
            continue
        text_file = TEXT / f"{path.stem}.txt"
        status = "ok"
        try:
            reader = PdfReader(str(path), strict=False)
            page_text: list[str] = []
            for page in reader.pages:
                page_text.append(page.extract_text() or "")
            text = "\n\n".join(page_text)
            text_file.write_text(text, encoding="utf-8")
            target_texts[file_name] = text
            docs.append({
                "file": file_name,
                "url": row.get("url", ""),
                "sha256": row.get("sha256", ""),
                "status": status,
                "pages": str(len(reader.pages)),
                "text_chars": str(len(text)),
                "text_file": str(text_file.relative_to(ROOT)),
            })
            for keyword in KEYWORDS:
                count = text.lower().count(keyword.lower())
                if count:
                    keyword_hits.append({"file": file_name, "keyword": keyword, "count": str(count)})
            for line in reference_lines(text):
                edges.append({"source": file_name, "target": "", "evidence": line})
        except Exception as exc:  # PDFs can be damaged or image-only.
            docs.append({
                "file": file_name,
                "url": row.get("url", ""),
                "sha256": row.get("sha256", ""),
                "status": f"extract-error:{type(exc).__name__}",
                "pages": "0",
                "text_chars": "0",
                "text_file": "",
            })
        if position % 10 == 0:
            print(f"indexed {position}/{len(rows)}", flush=True)

    # Candidate edges are intentionally conservative: they require an alias to
    # occur in the source text.  These are review targets, not proof of a
    # citation relationship.
    for source, text in target_texts.items():
        lower = text.lower()
        for target, aliases in TITLE_ALIASES.items():
            for alias in aliases:
                if alias.lower() in lower and source != alias:
                    edges.append({
                        "source": source,
                        "target": target,
                        "evidence": f"title-alias:{alias}",
                    })
                    break

    with docs_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["file", "url", "sha256", "status", "pages", "text_chars", "text_file"])
        writer.writeheader()
        writer.writerows(docs)
    with edges_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["source", "target", "evidence"], delimiter="\t")
        writer.writeheader()
        writer.writerows(edges)
    with keywords_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["file", "keyword", "count"], delimiter="\t")
        writer.writeheader()
        writer.writerows(keyword_hits)
    print(f"documents={len(docs)} candidate_edges={len(edges)} keyword_hits={len(keyword_hits)}", flush=True)


if __name__ == "__main__":
    main()
