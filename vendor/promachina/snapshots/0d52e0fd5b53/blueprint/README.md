# IUT Lean Blueprint

This directory contains the LeanBlueprint source for the IUT Lean
formalization project.

Build and check everything locally with:

```bash
leanblueprint all
```

This builds the printable PDF, builds the HTML/dependency-graph site, builds
the Lean project, and checks every declaration listed in `lean_decls`.

The local render toolchain is expected to include `latexmk`, `xelatex`,
`kpsewhich`, `gs`, `pdf2svg`, `dvisvgm`, and Graphviz `dot`. On macOS with
Homebrew, these are supplied by:

```bash
brew install texlive pdf2svg dvisvgm graphviz
```

The printable output is written to `print/print.pdf`; the HTML output is
written to `web/index.html`.

Check that every Lean declaration listed in `lean_decls` still resolves with:

```bash
leanblueprint checkdecls
```

The source files live under `src/`. The first draft is intentionally detailed
through the Stage 1 target, namely the corridor from IUT III, Theorem 3.11 to
Corollary 3.12. Later IUT IV and arithmetic consequences are only high-level
roadmap nodes for now.
