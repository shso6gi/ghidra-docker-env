# Paper authoring rules

- `main.tex` is the build entry point. Keep chapter text in the numbered files under `sections/`.
- Write Japanese prose in だ・である style. Use `，` and `．` for Japanese punctuation.
- Treat `tech-sample-css.tex` as the authoritative format. Keep the `main.tex` preamble identical through `\begin{document}`; change research content, not its document class, packages, or template macros.
- Treat `tech-sample-css.pdf` as the output reference. Do not copy the sample title, authors, affiliations, abstracts, figures, or submission instructions into `main.tex`.
- Do not invent evaluation counts, performance claims, bibliographic facts, author metadata, or submission requirements. Leave a specific `TODO(...)` comment until evidence is fixed.
- Distinguish facts verified from code or experiment artifacts from interpretations. State validation scope with every empirical claim.
- Use `対象の2つのバイナリ` when referring to the compared binaries. Avoid spatial labels such as `左右` unless describing a figure layout.
- Escape LaTeX special characters in prose, including underscores in result names such as `NOT\_EQ`.
- Keep acknowledgments immediately before the reference list. Use the template's `thebibliography` environment unless the official CSS kit's `ipsjunsrt.bst` is added explicitly.
- Run `make check-template` after changing `main.tex`. Run `make build` after meaningful changes. Check `build/main.log` for errors, warnings, and overfull boxes, then inspect all pages of `build/main.pdf` when layout changes.
- Do not add files under `build/` to version control.
