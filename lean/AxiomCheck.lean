module

public meta import Lean.Elab.Command

/-!
`#print axioms foo` reports its result as an *info* message, so it never fails a build.
A CI job running `lake build` would happily go green on a proof that depends on `sorryAx`.

This module provides `#check_axioms foo`, which is silent on success
and throws a genuine elaboration **error** when `foo` depends on anything
outside the three standard axioms of classical Lean.
-/

open Lean Elab Command

-- The three axioms of standard classical Lean/Mathlib.
private meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#check_axioms foo` succeeds silently if `foo` depends only on the standard
classical axioms, and fails the build otherwise. -/
syntax (name := checkAxiomsCmd) "#check_axioms " ident : command

@[command_elab checkAxiomsCmd]
public meta def elabCheckAxioms : CommandElab := fun (stx : Syntax) => do
  let ident := stx[1]
  -- `realizeGlobalConstWithInfos` resolves the name *and* registers a hover / go-to-definition link.
  let cs ← liftCoreM (realizeGlobalConstWithInfos ident)
  for c in cs do
    let axs ← collectAxioms c
    let bad := axs.filter (fun a => !standardAxioms.contains a)
    unless bad.isEmpty do
      throwError "{c} depends on non-standard axioms: {bad.toList}"
