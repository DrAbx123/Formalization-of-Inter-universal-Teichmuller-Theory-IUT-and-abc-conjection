from __future__ import annotations

import csv
import re
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1] / "papers" / "motizuki_corpus"

LABEL_TARGETS = {
    "IUTchI": "Inter-universal Teichmuller Theory I.pdf",
    "IUTchII": "Inter-universal Teichmuller Theory II.pdf",
    "IUTchIII": "Inter-universal Teichmuller Theory III.pdf",
    "IUTchIV": "Inter-universal Teichmuller Theory IV.pdf",
    "Pano": "Panoramic Overview of Inter-universal Teichmuller Theory.pdf",
    "EssLgc": "Essential Logical Structure of Inter-universal Teichmuller Theory.pdf",
    "Alien": "Alien Copies, Gaussians, and Inter-universal Teichmuller Theory.pdf",
    "EtTh": "The Etale Theta Function and its Frobenioid-theoretic Manifestations.pdf",
    "FrdI": "The Geometry of Frobenioids I.pdf",
    "FrdII": "The Geometry of Frobenioids II.pdf",
    "HASurI": "A Survey of the Hodge-Arakelov Theory of Elliptic Curves I.pdf",
    "HASurII": "A Survey of the Hodge-Arakelov Theory of Elliptic Curves II.pdf",
    "GenEll": "Arithmetic Elliptic Curves in General Position.pdf",
    "pOrd": "A Theory of Ordinary p-adic Curves.pdf",
    "pTch": "Foundations (comments).pdf",
    "pTchIn": "An Introduction to p-adic Teichmuller Theory.pdf",
    "GeoAnbd": "The Geometry of Anabelioids.pdf",
    "AbsAnab": "Absolute Anabelian Geometry.pdf",
    "NCBelyi": "Noncritical Belyi Maps.pdf",
    "Semi": "Semi-graphs of Anabelioids.pdf",
    "Cusp": "Absolute Anabelian Cuspidalizations.pdf",
    "CmbGC": "Combinatorial Grothendieck Conjecture.pdf",
    "CmbCsp": "Combinatorial Cuspidalization.pdf",
    "CbTpI": "Combinatorial Anabelian Topics I.pdf",
    "CbTpII": "Combinatorial Anabelian Topics II.pdf",
    "CbTpIII": "Combinatorial Anabelian Topics III.pdf",
    "CbTpIV": "Combinatorial Anabelian Topics IV.pdf",
    "Mzk1": "The Hodge-Arakelov Theory of Elliptic Curves.pdf",
    "Mzk2": "The Scheme-theoretic Theta Convolution.pdf",
    "Mzk3": "Connections and Related Structures on the Universal Extension of an Elliptic Curve.PDF",
}


def main() -> None:
    known_files = {row["file"] for row in csv.DictReader((ROOT / "pdfs.csv").open(encoding="utf-8-sig"))}
    edges: set[tuple[str, str, str, str]] = set()
    unresolved: Counter[str] = Counter()
    snippets_path = ROOT / "reference_snippets.tsv"
    with snippets_path.open(encoding="utf-8", newline="") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            source = row["source"]
            text = row["text"]
            for label, target in LABEL_TARGETS.items():
                if not re.search(rf"(?<![A-Za-z]){re.escape(label)}(?![A-Za-z])", text, re.IGNORECASE):
                    continue
                if target not in known_files:
                    unresolved[label] += 1
                    continue
                if source != target:
                    edges.add((source, target, label, row["line"]))
            # Keep bracketed labels that are not mapped so the mapping can be
            # extended without losing evidence from this pass.
            for label in re.findall(r"\[([A-Za-z][A-Za-z0-9_-]{2,})\]", text):
                if label not in LABEL_TARGETS:
                    unresolved[label] += 1

    with (ROOT / "citation_edges.tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["source", "target", "label", "source_line"], delimiter="\t")
        writer.writeheader()
        for source, target, label, line in sorted(edges):
            writer.writerow({"source": source, "target": target, "label": label, "source_line": line})

    indegree: Counter[str] = Counter()
    outdegree: Counter[str] = Counter()
    for source, target, _label, _line in edges:
        outdegree[source] += 1
        indegree[target] += 1
    with (ROOT / "citation_nodes.tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["file", "incoming", "outgoing"], delimiter="\t")
        writer.writeheader()
        for file_name in sorted(known_files | set(indegree) | set(outdegree)):
            writer.writerow({"file": file_name, "incoming": indegree[file_name], "outgoing": outdegree[file_name]})

    with (ROOT / "unresolved_reference_labels.tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t")
        writer.writerow(["label", "occurrences"])
        writer.writerows(sorted(unresolved.items(), key=lambda item: (-item[1], item[0])))
    print(f"resolved_edges={len(edges)} unresolved_labels={len(unresolved)}")


if __name__ == "__main__":
    main()
