# IUT III Theorem 3.11 原文快照索引

## 快照元数据

- `ID`: 1
- `sourceVersion`: `Inter-universal Teichmuller Theory III`, Shinichi Mochizuki, May 2020 (the version stored in this repository)
- `sourcePdf`: `papers/motizuki_corpus/raw/Inter-universal Teichmuller Theory III.pdf`
- `sourceSha256`: `9A7EE3C77B1C7717210C0613EB39B6844649D0040DC3D9E1BE7D544F8F91A0B9`
- `pdfPhysicalPageCount`: 199
- `lockedPhysicalPages`: 153--159
- `formulaAuthority`: rendered PDF; extracted text is a locating index only
- `extraction`: `pypdf plain` and `pypdf layout`
- `pdfMetadata`: title `iu-teich-3.pdf`; creator `TeX output 2020.05.18:2324`; creation date 2020-05-18; page size A4; PDF version 1.5

The raw PDF and both focused extracts are the immutable source artifacts for
this task. The focused extract headers retain the historical source path,
SHA-256, page count, selected pages, and extraction mode. Do not treat
extracted glyphs as an authoritative transcription of decorated formulas.

## Citation index

The continuous-text line numbers below refer to
`papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`.
The focused plain/layout line numbers are file line numbers in the paired
page-delimited extracts listed below.

| segment | physical pages | continuous text lines | focused plain/layout anchors | source references and scope |
|---|---:|---:|---:|---|
| theorem opening and input | 153 | 9151--9163 | plain line 11--23; page 153 marker line 8 | Theorem 3.11 title; initial Theta-data; distinct `Theta+-ell-NF` Hodge-theater family; D-theater determined up to isomorphism by vertical coricity |
| (i) multiradial representation | 153--155 | 9164--9295 | plain line 24--147 and 150--157; page markers 8, 67, 148 | procession; (a) local packets/integral structures and normalized log-volumes; (b) bad-place splitting monoid; (c) number fields and global Frobenioids; Ind1/Ind2; functoriality and permutation compatibility |
| (ii) log-Kummer correspondence | 155--156 | 9296--9449 | plain line 158--312; page markers 148, 269 | labelled Kummer isomorphisms; local packet, splitting-monoid, number-field/Frobenioid isomorphisms; MOD/mod compatibility; Ind3 upper-semi directions (`subseteq` nonarchimedean, `surjects` archimedean); log-volume compatibility |
| (iii) Theta-times-mu LGP-link compatibility | 156--159 | 9450--9615 | plain line 313--476 and 479--481; page markers 269, 343, 415, 477 | horizontal link compatibility for (a) unit prime-strips, (b) environment strips, (c) `n,◦R` and permutation symmetries, (d) Kummer/evaluation maps; stabilized/equivariant/functorial conclusion up to Ind1--Ind3 |
| printed proof | 159 | 9616--9618 | plain line 482--484; page 159 marker line 477 | proof refers the assertions immediately to definitions and cited references; it is not an independent construction record |

Subsection anchors in the continuous text are: (i) header 9164, (i)(a) 9176,
(i)(b) 9192, (i)(c) 9222, Ind1/Ind2 9254--9272, and functoriality/permutation
compatibility 9273--9295; (ii) header 9296, (ii)(a) 9321, (ii)(b) 9365,
(ii)(c) 9372, Ind3 9439--9446, and log-volume compatibility 9447--9449;
(iii) header 9450, (iii)(a) 9455, (iii)(b) 9483, (iii)(c) 9518,
(iii)(d) 9566, and final compatibility 9566--9615.

### Focused extract files

- `IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt`
- `IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.layout.txt`
- `IUTIII_Theorem311_through_Corollary312_pp153-186.plain.txt` (longer corridor extract retaining pp.160--172)
- `IUTIII_Theorem311_through_Corollary312_pp153-186.layout.txt`

## Task status and evidence

- `STATUS A1`: `source-audit-complete/interface`
- `status`: `source-audit-complete/interface`
- `mathematicalProofClaim`: `false`
- `Lean file/declaration`: `N/A` (artifact-only task; no new Lean declaration)
- `constructed source artifact`: version-locked PDF, paired page-delimited extracts, and this citation index; no IUT mathematical object is constructed here
- `verification`: `tools/check_source_text_audit.ps1`, exit code 0; `logs/source-audit/run-20260813-143520/summary.json` reports `passed: true`, matching PDF hashes and all expected page markers, with `mathematicalProofClaim: false`
- `Lean compile`, `warning count`, `#print axioms`, `sorryAx`, and custom-axiom checks: `N/A` for this artifact-only task; this entry does not upgrade Theorem 3.11 status
- `statusDate`: 2026-08-13
