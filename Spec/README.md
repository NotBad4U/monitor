# Spec

Typst sources for the specification *Mealy: a FLTL4 monitor*.

There are two main files, each compiled on its own:

- `main.typ`: the full spec.
- `formula-sheet.typ`: a quick reference listing every formula of the spec.

> [!NOTE]
> The formula sheet (`formula-sheet.typ`) has no formulas of its own: it imports them from the section files,
> so editing a formula in the spec updates the sheet too.

## Layout

| File | Content |
| --- | --- |
| `main.typ` | Entry point: document setup |
| `common.typ` | Shared package imports and macros, imported by every section |
| `intro.typ` | Context and overview of runtime verification |
| `preliminaries.typ` | Traces, truth domains, LTL and FLTL |
| `fltl4.typ` | The logic FLTL4 and its monitor as a Mealy machine |
| `enhanced-m4.typ` | Enhanced Mealy: profunctor composition, anticipation |
| `metric-fltl4.typ` | Timed extensions: metric and timed propositional variants |
| `development.typ` | Development overview in Lean (TODO) |
| `formula-sheet.typ` | Standalone sheet listing every formula, imported from the sections |
| `refs.bib` | Bibliography |

## Build

```sh
typst compile main.typ           # full spec
typst compile formula-sheet.typ  # formula sheet
```
