# arXiv pre-flight report

Date: 25 September 2026.

No arXiv submission was made.

## Authoritative guidance checked

Current arXiv documentation checked during preparation:

- TeX/LaTeX submission requirements: https://info.arxiv.org/help/submit_tex.html
- Metadata for required and optional fields: https://info.arxiv.org/help/prep.html
- arXiv license information: https://info.arxiv.org/help/license/index.html
- arXiv category taxonomy: https://arxiv.org/category_taxonomy

Relevant requirements reflected in the bundle:

- arXiv processes TeX submissions automatically and requires the submitter to inspect the generated PDF during submission.
- Source bundles should include only files needed for processing and should not include generated auxiliary files, logs, journal templates, referee letters, or unused assets.
- `\today` is avoided.
- PDFLaTeX is supported; no shell escape, minted, local fonts, generated figure conversions, or JavaScript are used.
- Metadata fields must be ASCII; the proposed title, author string, abstract, comments, and category recommendation below are ASCII-safe.
- Generative AI tools are not authors.
- `math.NT` is the recommended primary category.
- License choice remains a submitter decision and is irrevocable for each arXiv version.

## Source bundle

Prepared upload bundle:

- `main.tex`

The bibliography is embedded using `thebibliography`, so no `.bib` or `.bbl` file is required for compilation. There are no figures, style files, or external inputs.

## Local build checks

Commands run:

```bash
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex

mkdir clean-build
unzip pascal-minus-one-arxiv-source.zip -d clean-build
cd clean-build
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

Results:

- Paper source build: passed.
- Clean source-bundle build: passed.
- Cross-references: resolved after the second LaTeX pass.
- Bibliography: embedded and rendered; no BibTeX/Biber dependency.
- Missing files: none.
- Undefined control sequences: none.
- Duplicate labels: none reported.
- Nonportable paths: none found.
- Source encoding: ASCII-only source file.
- arXiv-hostile dependencies: none found.
- JavaScript, media, generated figure conversions: none.
- TODO/FIXME/DRAFT placeholder scan: no draft markers found; the word `placeholder` appears only in the formal-verification sentence about absence of proof placeholders.
- PDF rendering inspection: passed using the PDF render-first workflow; all 8 pages rendered.

Warnings reviewed:

- Three underfull hbox warnings remain. They occur in theorem-name and bibliography paragraphs and do not affect correctness or rendering.
- No overfull hbox warnings remain after line-wrapping the theorem-name list.

## Repository checks

The handoff `main` commit was verified as `d4a8d4c93c5dda22829774857c13df81d17fb989` before paper work began. The GitHub workflow query for that commit returned no pull-request-triggered runs through the connector, so local paper checks are recorded separately from repository CI history.

The paper source does not alter any Lean file or theorem statement. The ordinary repository CI workflow remains configured to run `lake update`, `lake build`, Python unit tests, the finite reference sweep, and the zero-sorry gate.

## Submission metadata recommendation

Title: `Restricted Binomial GCDs at Primes Congruent to -1`

Author string: `John Fairfax-Ball`

Primary category: `math.NT`

Optional MSC class: `11B65`

Comments field: `8 pages. Lean 4 / Mathlib formalization available in the linked repository. Palomar record PALOMAR-2026-09-25-000017, version 1.`

License recommendation: choose a license intentionally at submission time. CC BY 4.0 is the most liberal standard arXiv option and is compatible with broad reuse, but the decision is irrevocable for the submitted version and should reflect journal/funder plans.

## Remaining manual checks for the later submission session

- Upload `pascal-minus-one-arxiv-source.zip` to arXiv, but do not include the locally compiled PDF unless arXiv explicitly asks for it.
- Confirm the generated arXiv preview PDF matches `pascal-minus-one-paper.pdf`.
- Confirm author identity/affiliation metadata in the arXiv web form.
- Confirm the license choice.
- Do not enter an arXiv ID, DOI, journal reference, or report number before arXiv or a journal actually assigns one.
