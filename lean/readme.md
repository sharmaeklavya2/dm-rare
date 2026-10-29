# Lean Proofs

Lean formalization of the proofs in the RARE (Response-Aware Rational Equilibrium) paper.
All main results of the existence, dynamics, and Nash-equilibrium sections are proved, with no `sorry`.
Only the main theorems (those listed in `RareForMarkets.lean`) are the target of the formalization;
auxiliary lemmas of the paper are formalized only insofar as the main proofs need them.

The file `RareForMarkets.lean` mentions the names (in lean) of our main theorems.
It also runs `#check_axioms` on every main theorem, so `lake build` fails if
any of them depends on `sorry` or custom axioms.
(The CI workflow in `.github/workflows/` currently runs only when triggered manually.)

**Steps to verify these results**:

1.  Compile the code (`lake build`) to ensure that all theorems have proofs.
2.  From `RareForMarkets/Defs/`, read `Market.lean`, `Rare.lean`, and `Misc.lean`.
    These files contain the definitions found in the 'Preliminaries' and
    'Properties of the Revenue Function' sections of the paper.
3.  `RareForMarkets/Exist/` contains results about the existence of RARE in various settings.
    From that directory, read `Defs.lean` for the definitions specific to this section.
    Then verify that the theorem statements in `Main.lean` match those in the paper.
4.  `RareForMarkets/Dynamics/` contains results on Dynamics that lead to RARE.
    From that directory, read `Defs.lean` for the definition of the dynamic.
    Then verify that `Main.lean` claims the following:
    * `dynamics_sellout` claims that every seller sells her good completely.
    * `dynamics_convergence` is the convergence theorem from the paper.
5.  `RareForMarkets/NashEq/` contains results that show that Nash equilibria usually don't exist in these markets.
    From that directory, read `Defs.lean` for the definition of Nash equilibrium.
    Then verify that the theorems in `NonRivalUncommon.lean` and `ReductionToRival.lean` match what the paper claims.

## Main Results

The statements of main theorems are in `Exist/Main.lean`, `Dynamics/Main.lean`,
`NashEq/NonRivalUncommon.lean`, and `NashEq/ReductionToRival.lean`;
each is a one-line wrapper around a `*_aux` lemma proved in the file listed below.

| LaTeX ref | Lean theorem name | Lean file containing the proof |
| --- | --- | --- |
| `thm:rare-exists-continuous` | `rare_exists_continuous` | `Exist/Continuous.lean` |
| `thm:rare-exists-continuous-corr` | `rare_exists_continuous_corr` | `Exist/Corollary.lean` |
| `thm:unique-nr-demand` | `unique_nr_demand` | `Exist/Unique.lean` |
| `thm:nonrival-rare-exists` | `nonrival_rare_exists` | `Exist/Concave.lean` |
| `thm:unique-rival-demand` | `unique_rival_demand` | `Exist/Unique.lean` |
| `thm:rival-rare-exists` | `rival_rare_exists` | `Exist/Concave.lean` |
| sellout during the dynamic | `dynamics_sellout` | `Dynamics/Proofs.lean` |
| `thm:dynamics-convergence` | `dynamics_convergence` | `Dynamics/Proofs.lean` |
| `thm:nasheq-uncommon` | `nasheq_uncommon` | `NashEq/Uncommon.lean` |
| `thm:rivalize-2` | `rivalize_allocRule_mem` | `NashEq/RivalizeDemand.lean` |
| `thm:rivalize-2` | `rivalize_isNashEq_iff` | `NashEq/RivalizeDemand.lean` |

The file `tex-labels.csv` maps each LaTeX label (e.g. `thm:rare-exists-continuous`) to its number in the paper's PDF.
It was generated from the repository root, after building the paper (`make -C paper`), by running

```bash
curl -fsSL -o /tmp/extractTexRefs.py https://raw.githubusercontent.com/sharmaeklavya2/extractTexRefs/main/extractTexRefs.py
python3 /tmp/extractTexRefs.py paper/build/dm-rare.aux --keys texLabel,type,outputId -o lean/tex-labels.csv
```

## Project Structure

This directory is the Lake project. The repository root additionally holds
`paper/` (the paper's LaTeX source) and the shared configuration
(`.devcontainer/`, `.github/`, `.claude/`).

| Path | Contents |
| --- | --- |
| `RareForMarkets.lean` | Root module: imports every part of the formalization and `#check_axioms` each main theorem. |
| `RareForMarkets/Defs/` | Markets, demand, allocation rules (`Market.lean`), RARE and limiting RARE (`Rare.lean`), scaled simplices (`Misc.lean`). |
| `RareForMarkets/Prelims.lean` | Results from `\cref{sec:prelims,sec:revenue-props}`. |
| `RareForMarkets/Exist/` | The existence section (see below). |
| `RareForMarkets/Dynamics/` | The dynamics section: `Defs.lean`, `Main.lean`, and `Proofs.lean` (`thm:vbound-pstar` as `exists_vbound`, monotonicity of prices, convergence). |
| `RareForMarkets/NashEq/` | The Nash-equilibrium section (see below). |
| `FixedPoint/` | Brouwer's fixed-point theorem and the KKM lemma, copied from [EconCSLib](https://github.com/gametheoryinlean/EconCSLib) (Apache 2.0). |
| `AxiomCheck.lean` | Defines `#check_axioms foo`, which fails the build if `foo` depends on anything beyond `propext`, `Classical.choice` and `Quot.sound` — in particular on `sorryAx`. `#print axioms` only emits an info message, so it cannot fail CI. |
| `tex-labels.csv` | Map from the paper's LaTeX labels to its theorem/section numbers (see [Main Results](#main-results)). |
| `scripts/lean-sig.py` | Prints a Lean file with tactic proofs stripped, leaving definitions and theorem statements. |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Build configuration, the pinned dependency revisions, and the pinned Lean version. |
| `CLAUDE.md` | Instructions for Claude Code (see [AI Use](#ai-use) below). |

Files in `RareForMarkets/Exist/`:

| File | Contents |
| --- | --- |
| `Defs.lean` | Security/overpricing parameters, welfare functions. |
| `Main.lean` | main theorem statements. |
| `Accounting.lean` | `thm:accounting`; identities for the parameters `ν`, `β`, `κ` (e.g. `κνβ = B`). |
| `InnerKKM.lean` | KKM over an arbitrary finite index type; `thm:general-inner-kkm`. |
| `Continuous.lean` | `thm:prop-box`, `thm:large-dev-deter`, `thm:rare-exists-continuous-2`, `thm:rare-exists-continuous`. |
| `Params.lean` | `thm:uniform-utility-improvement`, `thm:security`, `thm:overpricing`, `thm:robust-params`, proved once for a family of markets indexed by `ε ∈ [0, 1]`. |
| `Corollary.lean` | `thm:rare-exists-continuous-corr`. |
| `Argmax.lean` | `thm:affordable-limits` and `thm:maximizer-limits`, as closedness of the graph of the argmax correspondence; uniqueness and continuity of strictly concave maximizers. |
| `Demand.lean` | Non-rivalrous and `W`-rivalrous demand as argmax correspondences; strict concavity of `W(u₁(x₁), …, uₙ(xₙ))`. |
| `Unique.lean` | `thm:unique-nr-demand`, `thm:unique-rival-demand`. |
| `Perturb.lean` | The perturbed markets `Ical^{(ε)}`. |
| `Limit.lean` | The limit argument shared by `thm:nonrival-rare-exists` and `thm:rival-rare-exists`. |
| `Concave.lean` | `thm:nonrival-rare-exists`, `thm:rival-rare-exists`. |

Files in `RareForMarkets/NashEq/`:

| File | Contents |
| --- | --- |
| `Defs.lean` | Nash equilibrium (`defn:nasheq`), SPLC utilities. |
| `NonRivalUncommon.lean` | main theorem statement for `thm:nasheq-uncommon`. |
| `TwoGoods.lean` | Helpers for two-good markets with unit budgets. |
| `Uncommon.lean` | Proof of `thm:nasheq-uncommon`. |
| `ReductionToRival.lean` | The rivalized market `Î`; main theorem statements for `thm:rivalize-2`. |
| `RivalizeUtil.lean` | Properties of the rivalized utility `ûᵢ` (`thm:rivalize-1`, item 1). |
| `Cutoff.lean` | Bounds on `u_min`, `u_max`, demand facts, and bang-per-buck cutoffs used for `thm:rivalize-1`. |
| `RivalizeDemand.lean` | Proofs of `thm:rivalize-1`, item 2, and `thm:rivalize-2`. |

`Scratch.lean` and `AiScratch.lean` are `.gitignore`d scratch files, declared as
Lake targets so they build on demand but are not part of `defaultTargets`.

### Differences from the paper

* `thm:large-dev-deter`: when the deviating seller is the only seller,
  her revenue is only bounded by `κνpⱼ` (not `νpⱼ`).
  This suffices for `thm:rare-exists-continuous`.
* The perturbed market uses `max ε 0` in place of `ε`, so that it is a valid market for every real `ε`.
  This agrees with the paper on `ε ∈ [0, 1]`.
* `thm:dynamics-convergence` is proved using the scaled total price increase
  `κν ∑ₖ (p^{(t+1)}_k − p^{(t)}_k)` in place of the paper's `g_t`;
  it bounds every seller's dissatisfaction, and its partial sums are at most `B`.

## Local Setup

Install [`elan`](https://github.com/leanprover/elan); it reads `lean-toolchain` and
fetches the pinned Lean version itself. Then in this directory:

```bash
lake exe cache get   # download pre-built Mathlib .olean files
lake build           # build all targets
```

If you want to run these commands from the repository root, pass `-d` instead:

```bash
lake -d lean exe cache get
lake -d lean build
```

This works because the root `lean-toolchain` is a symlink to `lean/lean-toolchain`:
`elan` resolves the toolchain from the current directory, which `lake -d` does not change.

## VS Code with Docker Dev-container

One can open this repository in a VS Code devcontainer.
See <https://code.visualstudio.com/docs/devcontainers/containers> for details.
The container is specified in the `.devcontainer` directory **at the repository root**,
so open the root rather than this directory; the Lean project is then at `/workspace/lean`.
This setup runs Lean 4 and Claude Code in a docker container.
Mathlib's build artifacts live in a named volume, and `lake exe cache get` runs on creation.

The container has no TeX installation — the paper is meant to be compiled on the host.

## AI Use

The lean proofs have been written using [Claude Code](https://code.claude.com) (Opus 5.5).
Claude Code was given the proofs in LaTeX and some guidance on proof-writing in Lean+Mathlib (see CLAUDE.md).
I (Eklavya Sharma) have carefully reviewed the definitions and theorem statements,
and I believe they accurately represent what the paper claims.
