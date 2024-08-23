/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Util.AddRelatedDecl
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The `to_app` attribute

Adding `@[to_app]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ⟶ Y` in some category
will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

This is useful for automatically generating lemmas which the simplifier can use even on expressions
.......

There is also a term elaborator `to_app_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic
open Qq

namespace CategoryTheory

/-- A variant of `eq_whisker` with a more convenient argument order for use in tactics.  -/
theorem eq_app' {C D : Cat} {f g : C ⟶ D} {η θ : f ⟶ g} (w : η = θ) (X : C) :
    η.app X = θ.app X :=
  congrArg (NatTrans.app · X) w

/-- Simplify an expression using only the axioms of a category. -/
def catAppSimp (e : Expr) : MetaM Simp.Result :=
  -- TODO: figure out which ones are necessary
  simpOnlyNames [
    --``Category.comp_id, ``Category.id_comp, ``Category.assoc,
    ``Cat.id_obj, ``Cat.id_map, ``Cat.comp_obj, ``Cat.comp_map,
    ``Cat.whiskerLeft_app, ``Cat.whiskerRight_app, ``Cat.id_app, ``Cat.comp_app,
    ``Cat.eqToHom_app] e
    (config := { decide := false })

/--
Given an equation `f = g` between 2-morphisms `X ⟶ Y` in an arbitrary bicategory (possibly after a
`∀` binder), get the corresponding equation in the bicategory `Cat`. -/
def to_appExpr (e : Expr) : MetaM Expr := do
  logInfo m!"e at start: {e}"
  let (args, _, conclusion) ← forallMetaTelescope (← inferType e)
  logInfo m!"args at start: {args}"

  -- Find bicategory metavariable
  let η := (Expr.getAppArgsN conclusion 2)[0]!
  let f := (Expr.getAppArgsN (← inferType η) 2)[0]!
  let D := (Expr.getAppArgsN (← inferType f) 2)[1]!
  let B_pre ← inferType D
  let B ← Meta.getMVars B_pre
  -- assign bicategory metavariable
  let CAT := B[0]!
  logInfo m!"cat: {CAT}"
  logInfo m!"catlvl: {← Meta.getDecLevel B_pre}"
  let u ← Meta.mkFreshLevelMVar
  let v ← Meta.mkFreshLevelMVar
  CAT.assign q(Cat.{v, u})
  -- Find & assign bicategory instance
  let args2 ← args.mapM instantiateMVars
  logInfo m!"args2: {args2}"
  let i := args2.findIdx? fun x => !x.hasExprMVar
  let inst := (← Meta.getMVars (args2.get! (i.get! + 1)))[0]!
  inst.assign (← synthInstanceQ q(Bicategory.{max v u, max v u} Cat.{v, u}))
  -- logInfo m!"mvars: {← Meta.getMVars (args2.get! (i.get! + 1))}"
  -- logInfo m!"inst: {inst}"

  -- assign metavariables again
  let args2 := ← args.mapM instantiateMVars
  logInfo m!"args2_instatiated: {args2}"
  let args3 := args2.map fun e => if e.hasExprMVar then none else (pure e)
  logInfo m!"args3: {args3}"
  let applied2 ← mkAppOptM' e args3
  logInfo m!"applied2: {applied2}"
  let applied ← instantiateMVars conclusion
  -- create the specialized term
  -- let applied := (mkAppN E args2)
  -- logInfo m!"applied: {applied}"
  let applied2 ← mkLambdaFVars ((← Meta.getMVars applied).map (Expr.mvar)) applied
  logInfo m!"E:{applied}"
  logInfo m!"APP: {applied2}"
  return applied2

/--
Given morphisms `f g : C ⟶ D` in the bicategory `Cat`, and an equation `η = θ` between 2-morphisms
(possibly after a `∀` binder), produce the equation `∀ (X : C), f.app X = g.app X`, and simplify
it using basic lemmas in `Cat`. -/
def toAppExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do
    logInfo m!"e: {e}"
    logInfo m!"e type: {← inferType e}"
    -- NOW IM HAVING A UNIVERSE ISSUE!!!
    simpType catAppSimp (← mkAppM ``eq_app' #[e])) e


/--
Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`, where `f g : X ⟶ Y` are
morphisms in some category, will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).
So, for example, if the conclusion of `F` is `a ≫ b = g` then
the conclusion of `F_assoc` will be `a ≫ (b ≫ h) = g ≫ h` (note that `≫` reassociates
to the right so the brackets will not appear in the statement).

This attribute is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

Note that if you want both the lemma and the reassociated lemma to be
`simp` lemmas, you should tag the lemma `@[reassoc (attr := simp)]`.
The variant `@[simp, reassoc]` on a lemma `F` will tag `F` with `@[simp]`,
but not `F_apply` (this is sometimes useful).
-/
syntax (name := to_app) "to_app" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `to_app
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_app $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`to_app` can only be used as a global attribute"
    addRelatedDecl src "_app" ref stx? fun type value levels => do
      -- NOTE: value: fun {B} [Bicategory B] ... => mapComp ...
      -- NOTE: type: ∀ {B} [Bicategory B] ... => mapComp ...
      logInfo m!"TYPE: {← mkExpectedTypeHint value type}"
      pure (← toAppExpr (← to_appExpr value), levels)
  | _ => throwUnsupportedSyntax }

open Term in
/--
`reassoc_of% t`, where `t` is
an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly after a `∀` binder),
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
-/
elab "to_app_of% " t:term : term => do
  logInfo m!"CAT: {(← elabTerm t none)}"
  logInfo m!"eq_app : {(← mkAppM ``eq_app' #[(← elabTerm t none)])}"
  -- this might be hackier than I want later? (requires providing args explicitly..)
  to_appExpr (← elabTerm t none)


end CategoryTheory
