# RARE: Response-Aware Rational Equilibrium in Pricing Games

This repository contains the paper
*RARE: Response-Aware Rational Equilibrium in Pricing Games*
by Bhaskar Ray Chaudhury, Jugal Garg, Xin Huang, and Eklavya Sharma,
together with a Lean 4 formalization of its main results.

## Contents

| Path | Contents |
| --- | --- |
| [`paper/`](paper/) | LaTeX source of the paper. See [`paper/readme.md`](paper/readme.md) for build instructions. |
| [`lean/`](lean/) | Lean 4 + Mathlib formalization (no `sorry`). See [`lean/readme.md`](lean/readme.md) for how to build and check it, and for the map from paper results to Lean theorems. |
| `.devcontainer/` | VS Code dev-container with Lean 4 and Claude Code (no TeX). |
| `.github/workflows/` | CI that runs `lake build` (currently triggered manually). |
| `lean-toolchain` | Symlink to `lean/lean-toolchain`, so `lake -d lean build` works from the root. |

## Quick start

Build the paper (needs a TeX installation):

```bash
make -C paper        # writes paper/build/dm-rare.pdf
```

Check the Lean proofs (needs [`elan`](https://github.com/leanprover/elan)):

```bash
lake -d lean exe cache get
lake -d lean build
```
