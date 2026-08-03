from __future__ import annotations

import csv
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1] / "papers" / "motizuki_corpus"
TEXT = ROOT / "text"

TARGETS = {
    "IUT-I": ("Inter-universal Teichmuller Theory I.pdf", [r"inter[- ]universal teichmuller theory i", r"\biut[- ]i\b"]),
    "IUT-II": ("Inter-universal Teichmuller Theory II.pdf", [r"inter[- ]universal teichmuller theory ii", r"\biut[- ]ii\b"]),
    "IUT-III": ("Inter-universal Teichmuller Theory III.pdf", [r"inter[- ]universal teichmuller theory iii", r"\biut[- ]iii\b"]),
    "IUT-IV": ("Inter-universal Teichmuller Theory IV.pdf", [r"inter[- ]universal teichmuller theory iv", r"\biut[- ]iv\b"]),
    "PANORAMIC": ("Panoramic Overview of Inter-universal Teichmuller Theory.pdf", [r"panoramic overview of inter[- ]universal teichmuller"]),
    "ESSENTIAL-LOGIC": ("Essential Logical Structure of Inter-universal Teichmuller Theory.pdf", [r"essential logical structure of inter[- ]universal teichmuller"]),
    "EXPLICIT-ESTIMATES": ("Explicit estimates in IUTeich.pdf", [r"explicit estimates in iuteich"]),
}


def normalized_lines(text: str) -> list[str]:
    return [re.sub(r"\s+", " ", line).strip() for line in text.splitlines()]


def main() -> None:
    edges: list[dict[str, str]] = []
    snippets: list[dict[str, str]] = []
    for source_path in sorted(TEXT.glob("*.txt")):
        source = source_path.name.removesuffix(".txt") + ".pdf"
        text = source_path.read_text(encoding="utf-8", errors="replace")
        lines = normalized_lines(text)
        lower = text.lower()
        for target_id, (target_file, patterns) in TARGETS.items():
            if source == target_file:
                continue
            for pattern in patterns:
                match = re.search(pattern, lower, flags=re.IGNORECASE)
                if not match:
                    continue
                start = max(0, match.start() - 140)
                end = min(len(text), match.end() + 220)
                evidence = re.sub(r"\s+", " ", text[start:end]).strip()
                edges.append({
                    "source": source,
                    "target": target_id,
                    "target_file": target_file,
                    "evidence": evidence,
                    "method": "title-alias-first-hit",
                })
                break
        in_refs = False
        for line_no, line in enumerate(lines, start=1):
            if re.match(r"^(references|bibliography|参考文献|文献)$", line, flags=re.IGNORECASE):
                in_refs = True
            if in_refs and line and any(
                key in line.lower()
                for key in ("mochizuki", "iut", "frobenioid", "hodge-arakelov", "teichmuller", "anabelian")
            ):
                snippets.append({"source": source, "line": str(line_no), "text": line[:1200]})

    with (ROOT / "citation_graph.tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["source", "target", "target_file", "evidence", "method"], delimiter="\t")
        writer.writeheader()
        writer.writerows(edges)
    with (ROOT / "reference_snippets.tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["source", "line", "text"], delimiter="\t")
        writer.writeheader()
        writer.writerows(snippets)
    print(f"edges={len(edges)} reference_snippets={len(snippets)}")


if __name__ == "__main__":
    main()
