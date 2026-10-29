# Paper

LaTeX source of the paper
*RARE: Response-Aware Rational Equilibrium in Pricing Games*
by Bhaskar Ray Chaudhury, Jugal Garg, Xin Huang, and Eklavya Sharma.

## Building

Requires `pdflatex` and `bibtex` (any recent TeX Live or MacTeX) and GNU `make`.
In this directory:

```bash
make            # full build (pdflatex, bibtex, then pdflatex three times)
make once       # a single pdflatex pass, for quick checks
make bib        # run bibtex only
```

The PDF is written to `build/dm-rare.pdf` (`build/` is `.gitignore`d).

Optional `make` variables:

| Variable | Effect |
| --- | --- |
| `COLOR=dark` | Color scheme: `light` (default), `sepia`, or `dark`. See `colorscheme.tex`. |
| `SILENT=1` | Run `pdflatex` in batch mode and `bibtex` with `-terse`. |
| `OUT_DIR=` | Write output files to this directory instead of `build/`. |

Example: `make COLOR=dark once`.

## Structure

| Path | Contents |
| --- | --- |
| `main.tex` | Top-level file: preamble, title, authors, and the list of sections. |
| `abstract.tex` | The abstract (kept separate so it can be pasted into submission forms). |
| `macros.tex` | Math macros. |
| `colorscheme.tex` | Text and link colors for the `light`, `sepia`, and `dark` schemes. |
| `bibdb.bib` | Bibliography. |
| `sec/` | The sections of the paper, each in a different tex file, `\input` from `main.tex`. |
| `figs/` | TikZ figures, `\input` from the sections. |

## Relation to the Lean formalization

The main results are formally verified in Lean 4; see [`../lean/readme.md`](../lean/readme.md).
That readme maps the paper's `\label`s (e.g. `thm:rare-exists-continuous`) to Lean theorem names.
