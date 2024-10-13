/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence.Datatypes

/-!
# Normalization of 2-morphisms in bicategories

This file provides a function that normalizes 2-morphisms in bicategories. The function also
used to normalize morphisms in monoidal categories. This is used in the string diagram widget given
in `Mathlib.Tactic.StringDiagram`, as well as `monoidal` and `bicategory` tactics.

We say that the 2-morphism `η` in a bicategory is in normal form if
1. `η` is of the form `α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₘ ≫ ηₘ ≫ αₘ₊₁` where each `αᵢ` is a
  structural 2-morphism (consisting of associators and unitors),
2. each `ηᵢ` is a non-structural 2-morphism of the form `f₁ ◁ ... ◁ fₙ ◁ θ`, and
3. `θ` is of the form `ι₁ ◫ ... ◫ ιₗ`, and
4. each `ιᵢ` is of the form `κ ▷ g₁ ▷ ... ▷ gₖ`.

Note that the horizontal composition `◫` is not currently defined for bicategories. In the monoidal
category setting, the horizontal composition is defined as the `tensorHom`, denoted by `⊗`.

Note that the structural morphisms `αᵢ` are not necessarily normalized, as the main purpose
is to get a list of the non-structural morphisms out.

Currently, the primary application of the normalization tactic in mind is drawing string diagrams,
which are graphical representations of morphisms in monoidal categories, in the infoview. When
drawing string diagrams, we often ignore associators and unitors (i.e., drawing morphisms in
strict monoidal categories). On the other hand, in Lean, it is considered difficult to formalize
the concept of strict monoidal categories due to the feature of dependent type theory. The
normalization tactic can remove associators and unitors from the expression, extracting the
necessary data for drawing string diagrams.

The string diagrams widget is to use Penrose (https://github.com/penrose) via ProofWidget.
However, it should be noted that the normalization procedure in this file does not rely on specific
settings, allowing for broader application. Future plans include the following. At least I (Yuma)
would like to work on these in the future, but it might not be immediate. If anyone is interested,
I would be happy to discuss.

- Currently, the string diagrams widget only do drawing. It would be better they also generate
  proofs. That is, by manipulating the string diagrams displayed in the infoview with a mouse to
  generate proofs. In #10581, the string diagram widget only uses the morphisms generated by the
  normalization tactic and does not use proof terms ensuring that the original morphism and the
  normalized morphism are equal. Proof terms will be necessary for proof generation.

- There is also the possibility of using homotopy.io (https://github.com/homotopy-io), a graphical
  proof assistant for category theory, from Lean. At this point, I have very few ideas regarding
  this approach.

## Main definitions
- `Tactic.BicategoryLike.eval`: Given a Lean expression `e` that represents a morphism in a monoidal
category, this function returns a pair of `⟨e', pf⟩` where `e'` is the normalized expression of `e`
and `pf` is a proof that `e = e'`.

-/

open Lean Meta

namespace Mathlib.Tactic.BicategoryLike

section

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRight : Type
  /-- Construct the expression for an atomic 2-morphism. -/
  | of (η : Atom) : WhiskerRight
  /-- Construct the expression for `η ▷ f`. -/
  | whisker (e : Mor₂) (η : WhiskerRight) (f : Atom₁) : WhiskerRight
  deriving Inhabited

/-- The underlying `Mor₂` term of a `WhiskerRight` term. -/
def WhiskerRight.e : WhiskerRight → Mor₂
  | .of η => .of η
  | .whisker e .. => e

/-- Expressions of the form `η₁ ⊗ ... ⊗ ηₙ`. -/
inductive HorizontalComp : Type
  | of (η : WhiskerRight) : HorizontalComp
  | cons (e : Mor₂) (η : WhiskerRight) (ηs : HorizontalComp) :
    HorizontalComp
  deriving Inhabited

/-- The underlying `Mor₂` term of a `HorizontalComp` term. -/
def HorizontalComp.e : HorizontalComp → Mor₂
  | .of η => η.e
  | .cons e .. => e

/-- Expressions of the form `f₁ ◁ ... ◁ fₙ ◁ η`. -/
inductive WhiskerLeft : Type
  /-- Construct the expression for a right-whiskered 2-morphism. -/
  | of (η : HorizontalComp) : WhiskerLeft
  /-- Construct the expression for `f ◁ η`. -/
  | whisker (e : Mor₂) (f : Atom₁) (η : WhiskerLeft) : WhiskerLeft
  deriving Inhabited

/-- The underlying `Mor₂` term of a `WhiskerLeft` term. -/
def WhiskerLeft.e : WhiskerLeft → Mor₂
  | .of η => η.e
  | .whisker e .. => e

/-- Whether a given 2-isomorphism is structural or not. -/
def Mor₂Iso.isStructural (α : Mor₂Iso) : Bool :=
  match α with
  | .structuralAtom _ => true
  | .comp _ _ _ _ η θ => η.isStructural && θ.isStructural
  | .whiskerLeft _ _ _ _ η => η.isStructural
  | .whiskerRight _ _ _ η _ => η.isStructural
  | .horizontalComp _ _ _ _ _ η θ => η.isStructural && θ.isStructural
  | .inv _ _ _ η => η.isStructural
  | .coherenceComp _ _ _ _ _ _ η θ => η.isStructural && θ.isStructural
  | .of _ => false

/-- Expressions for structural isomorphisms. We do not impose the condition `isStructural` since
it is not needed to write the tactic. -/
abbrev Structural := Mor₂Iso

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for a structural 2-morphism. -/
  | nil (e : Mor₂) (α : Structural) : NormalExpr
  /-- Construct the normalized expression of a 2-morphism `α ≫ η ≫ ηs` recursively. -/
  | cons (e : Mor₂) (α : Structural) (η : WhiskerLeft) (ηs : NormalExpr) : NormalExpr
  deriving Inhabited

/-- The underlying `Mor₂` term of a `NormalExpr` term. -/
def NormalExpr.e : NormalExpr → Mor₂
  | .nil e .. => e
  | .cons e .. => e

/-- A monad equipped with the ability to construct `WhiskerRight` terms. -/
class MonadWhiskerRight (m : Type → Type) where
  /-- The expression for the right whiskering `η ▷ f`. -/
  whiskerRightM (η : WhiskerRight) (f : Atom₁) : m WhiskerRight

/-- A monad equipped with the ability to construct `HorizontalComp` terms. -/
class MonadHorizontalComp (m : Type → Type) extends MonadWhiskerRight m where
  /-- The expression for the horizontal composition `η ◫ ηs`. -/
  hConsM (η : WhiskerRight) (ηs : HorizontalComp) : m HorizontalComp

/-- A monad equipped with the ability to construct `WhiskerLeft` terms. -/
class MonadWhiskerLeft (m : Type → Type) extends MonadHorizontalComp m where
  /-- The expression for the left whiskering `f ▷ η`. -/
  whiskerLeftM (f : Atom₁) (η : WhiskerLeft) : m WhiskerLeft

/-- A monad equipped with the ability to construct `NormalExpr` terms. -/
class MonadNormalExpr (m : Type → Type) extends MonadWhiskerLeft m where
  /-- The expression for the structural 2-morphism `α`. -/
  nilM (α : Structural) : m NormalExpr
  /-- The expression for the normalized 2-morphism `α ≫ η ≫ ηs`. -/
  consM (headStructural : Structural) (η : WhiskerLeft) (ηs : NormalExpr) : m NormalExpr

variable {m : Type → Type} [Monad m]

open MonadMor₁

/-- The domain of a 2-morphism. -/
def WhiskerRight.srcM [MonadMor₁ m] : WhiskerRight → m Mor₁
  | WhiskerRight.of η => return η.src
  | WhiskerRight.whisker _ η f => do comp₁M (← η.srcM) (.of f)

/-- The codomain of a 2-morphism. -/
def WhiskerRight.tgtM [MonadMor₁ m] : WhiskerRight → m Mor₁
  | WhiskerRight.of η => return η.tgt
  | WhiskerRight.whisker _ η f => do comp₁M (← η.tgtM) (.of f)

/-- The domain of a 2-morphism. -/
def HorizontalComp.srcM [MonadMor₁ m] : HorizontalComp → m Mor₁
  | HorizontalComp.of η => η.srcM
  | HorizontalComp.cons _ η ηs => do comp₁M (← η.srcM) (← ηs.srcM)

/-- The codomain of a 2-morphism. -/
def HorizontalComp.tgtM [MonadMor₁ m] : HorizontalComp → m Mor₁
  | HorizontalComp.of η => η.tgtM
  | HorizontalComp.cons _ η ηs => do comp₁M (← η.tgtM) (← ηs.tgtM)

/-- The domain of a 2-morphism. -/
def WhiskerLeft.srcM [MonadMor₁ m] : WhiskerLeft → m Mor₁
  | WhiskerLeft.of η => η.srcM
  | WhiskerLeft.whisker _ f η => do comp₁M (.of f) (← η.srcM)

/-- The codomain of a 2-morphism. -/
def WhiskerLeft.tgtM [MonadMor₁ m] : WhiskerLeft → m Mor₁
  | WhiskerLeft.of η => η.tgtM
  | WhiskerLeft.whisker _ f η => do comp₁M (.of f) (← η.tgtM)

/-- The domain of a 2-morphism. -/
def NormalExpr.srcM [MonadMor₁ m] : NormalExpr → m Mor₁
  | NormalExpr.nil _ η => η.srcM
  | NormalExpr.cons _ α _ _ => α.srcM

/-- The codomain of a 2-morphism. -/
def NormalExpr.tgtM [MonadMor₁ m] : NormalExpr → m Mor₁
  | NormalExpr.nil _ η => η.tgtM
  | NormalExpr.cons _ _ _ ηs => ηs.tgtM

namespace NormalExpr

variable [MonadMor₂Iso m] [MonadNormalExpr m]

/-- The identity 2-morphism as a term of `normalExpr`. -/
def idM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| .structuralAtom <| ← MonadMor₂Iso.id₂M f

/-- The associator as a term of `normalExpr`. -/
def associatorM (f g h : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| .structuralAtom <| ← MonadMor₂Iso.associatorM f g h

/-- The inverse of the associator as a term of `normalExpr`. -/
def associatorInvM (f g h : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| ← MonadMor₂Iso.symmM <|
    .structuralAtom <| ← MonadMor₂Iso.associatorM f g h

/-- The left unitor as a term of `normalExpr`. -/
def leftUnitorM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| .structuralAtom <| ← MonadMor₂Iso.leftUnitorM f

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def leftUnitorInvM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| ← MonadMor₂Iso.symmM <| .structuralAtom <| ← MonadMor₂Iso.leftUnitorM f

/-- The right unitor as a term of `normalExpr`. -/
def rightUnitorM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| .structuralAtom <| ← MonadMor₂Iso.rightUnitorM f

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def rightUnitorInvM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| ← MonadMor₂Iso.symmM <| .structuralAtom <| ← MonadMor₂Iso.rightUnitorM f

/-- Construct a `NormalExpr` expression from a `WhiskerLeft` expression. -/
def ofM [MonadMor₁ m] (η : WhiskerLeft) : m NormalExpr := do
  MonadNormalExpr.consM ((.structuralAtom <| ← MonadMor₂Iso.id₂M (← η.srcM))) η
    (← MonadNormalExpr.nilM ((.structuralAtom <| ← MonadMor₂Iso.id₂M (← η.tgtM))))

/-- Construct a `NormalExpr` expression from a Lean expression for an atomic 2-morphism. -/
def ofAtomM [MonadMor₁ m] (η : Atom) : m NormalExpr :=
  NormalExpr.ofM <| .of <| .of <| .of η

end NormalExpr

/-- Convert a `NormalExpr` expression into a list of `WhiskerLeft` expressions. -/
def NormalExpr.toList : NormalExpr → List WhiskerLeft
  | NormalExpr.nil _ _ => []
  | NormalExpr.cons _ _ η ηs => η :: NormalExpr.toList ηs

end

section

/-- The result of evaluating an expression into normal form. -/
structure Eval.Result where
  /-- The normalized expression of the 2-morphism. -/
  expr : NormalExpr
  /-- The proof that the normalized expression is equal to the original expression. -/
  proof : Expr
  deriving Inhabited

variable {m : Type → Type} [Monad m]

/-- Evaluate the expression `α ≫ β`. -/
class MkEvalComp (m : Type → Type) where
  /-- Evaluate `α ≫ β` -/
  mkEvalCompNilNil (α β : Structural) : m Expr
  /-- Evaluate `α ≫ (β ≫ η ≫ ηs)` -/
  mkEvalCompNilCons (α β : Structural) (η : WhiskerLeft) (ηs : NormalExpr) : m Expr
  /-- Evaluate `(α ≫ η ≫ ηs) ≫ θ` -/
  mkEvalCompCons (α : Structural) (η : WhiskerLeft) (ηs θ ι : NormalExpr) (e_η : Expr) : m Expr

/-- Evaluatte the expression `f ◁ η`. -/
class MkEvalWhiskerLeft (m : Type → Type) where
  /-- Evaluatte `f ◁ α` -/
  mkEvalWhiskerLeftNil (f : Mor₁) (α : Structural) : m Expr
  /-- Evaluate `f ◁ (α ≫ η ≫ ηs)`. -/
  mkEvalWhiskerLeftOfCons (f : Atom₁) (α : Structural) (η : WhiskerLeft) (ηs θ : NormalExpr)
    (e_θ : Expr) : m Expr
  /-- Evaluate `(f ≫ g) ◁ η` -/
  mkEvalWhiskerLeftComp (f g : Mor₁) (η η₁ η₂ η₃ η₄ : NormalExpr)
    (e_η₁ e_η₂ e_η₃ e_η₄ : Expr) : m Expr
  /-- Evaluate `𝟙 _ ◁ η` -/
  mkEvalWhiskerLeftId (η η₁ η₂ : NormalExpr) (e_η₁ e_η₂ : Expr) : m Expr

/-- Evaluate the expression `η ▷ f`. -/
class MkEvalWhiskerRight (m : Type → Type) where
  /-- Evaluate `η ▷ f` -/
  mkEvalWhiskerRightAuxOf (η : WhiskerRight) (f : Atom₁) : m Expr
  /-- Evaluate `(η ◫ ηs) ▷ f` -/
  mkEvalWhiskerRightAuxCons (f : Atom₁) (η : WhiskerRight) (ηs : HorizontalComp)
    (ηs' η₁ η₂ η₃ : NormalExpr) (e_ηs' e_η₁ e_η₂ e_η₃ : Expr) : m Expr
  /-- Evaluate `α ▷ f` -/
  mkEvalWhiskerRightNil (α : Structural) (f : Mor₁) : m Expr
  /-- Evaluate ` (α ≫ η ≫ ηs) ▷ j` -/
  mkEvalWhiskerRightConsOfOf (f : Atom₁) (α : Structural) (η : HorizontalComp)
    (ηs ηs₁ η₁ η₂ η₃ : NormalExpr)
    (e_ηs₁ e_η₁ e_η₂ e_η₃ : Expr) : m Expr
  /-- Evaluate `(α ≫ (f ◁ η) ≫ ηs) ▷ g` -/
  mkEvalWhiskerRightConsWhisker (f : Atom₁) (g : Mor₁) (α : Structural) (η : WhiskerLeft)
    (ηs η₁ η₂ ηs₁ ηs₂ η₃ η₄ η₅ : NormalExpr) (e_η₁ e_η₂ e_ηs₁ e_ηs₂ e_η₃ e_η₄ e_η₅ : Expr) : m Expr
  /-- Evaluate `η ▷ (g ⊗ h)` -/
  mkEvalWhiskerRightComp (g h : Mor₁)
    (η η₁ η₂ η₃ η₄ : NormalExpr) (e_η₁ e_η₂ e_η₃ e_η₄ : Expr) : m Expr
  /-- Evaluate `η ▷ 𝟙 _` -/
  mkEvalWhiskerRightId (η η₁ η₂ : NormalExpr) (e_η₁ e_η₂ : Expr) : m Expr

/-- Evaluate the expression `η ◫ θ`. -/
class MkEvalHorizontalComp (m : Type → Type) where
  /-- Evaluate `η ◫ θ` -/
  mkEvalHorizontalCompAuxOf (η : WhiskerRight) (θ : HorizontalComp) : m Expr
  /-- Evaluate `(η ◫ ηs) ◫ θ` -/
  mkEvalHorizontalCompAuxCons (η : WhiskerRight) (ηs θ : HorizontalComp)
    (ηθ η₁ ηθ₁ ηθ₂ : NormalExpr) (e_ηθ e_η₁ e_ηθ₁ e_ηθ₂ : Expr) : m Expr
  /-- Evaluate `(f ◁ η) ◫ θ` -/
  mkEvalHorizontalCompAux'Whisker (f : Atom₁) (η θ : WhiskerLeft)
    (ηθ ηθ₁ ηθ₂ ηθ₃ : NormalExpr) (e_ηθ e_ηθ₁ e_ηθ₂ e_ηθ₃ : Expr) : m Expr
  /-- Evaluate `η ◫ (f ◁ θ)` -/
  mkEvalHorizontalCompAux'OfWhisker (f : Atom₁) (η : HorizontalComp) (θ : WhiskerLeft)
    (η₁ ηθ ηθ₁ ηθ₂ : NormalExpr) (e_ηθ e_η₁ e_ηθ₁ e_ηθ₂ : Expr) : m Expr
  /-- Evaluate `α ◫ β` -/
  mkEvalHorizontalCompNilNil (α β : Structural) : m Expr
  /-- Evaluate `α ◫ (β ≫ η ≫ ηs)` -/
  mkEvalHorizontalCompNilCons (α β : Structural) (η : WhiskerLeft)
    (ηs η₁ ηs₁ η₂ η₃ : NormalExpr) (e_η₁ e_ηs₁ e_η₂ e_η₃ : Expr) : m Expr
  /-- Evaluate `(α ≫ η ≫ ηs) ◫ β` -/
  mkEvalHorizontalCompConsNil (α β : Structural) (η : WhiskerLeft) (ηs : NormalExpr)
    (η₁ ηs₁ η₂ η₃ : NormalExpr) (e_η₁ e_ηs₁ e_η₂ e_η₃ : Expr) : m Expr
  /-- Evaluate `(α ≫ η ≫ ηs) ◫ (β ≫ θ ≫ θs)` -/
  mkEvalHorizontalCompConsCons (α β : Structural) (η θ : WhiskerLeft)
    (ηs θs ηθ ηθs ηθ₁ ηθ₂ : NormalExpr) (e_ηθ e_ηθs e_ηθ₁ e_ηθ₂ : Expr) : m Expr

/-- Evaluate the expression of a 2-morphism into a normalized form. -/
class MkEval (m : Type → Type) extends
    MkEvalComp m, MkEvalWhiskerLeft m, MkEvalWhiskerRight m, MkEvalHorizontalComp m where
  /-- Evaluate the expression `η ≫ θ` into a normalized form. -/
  mkEvalComp (η θ : Mor₂) (η' θ' ηθ : NormalExpr) (e_η e_θ e_ηθ : Expr) : m Expr
  /-- Evaluate the expression `f ◁ η` into a normalized form. -/
  mkEvalWhiskerLeft (f : Mor₁) (η : Mor₂) (η' θ : NormalExpr) (e_η e_θ : Expr) : m Expr
  /-- Evaluate the expression `η ▷ f` into a normalized form. -/
  mkEvalWhiskerRight (η : Mor₂) (h : Mor₁) (η' θ : NormalExpr) (e_η e_θ : Expr) : m Expr
  /-- Evaluate the expression `η ◫ θ` into a normalized form. -/
  mkEvalHorizontalComp (η θ : Mor₂) (η' θ' ι : NormalExpr) (e_η e_θ e_ι : Expr) : m Expr
  /-- Evaluate the atomic 2-morphism `η` into a normalized form. -/
  mkEvalOf (η : Atom) : m Expr
  /-- Evaluate the expression `η ⊗≫ θ := η ≫ α ≫ θ` into a normalized form. -/
  mkEvalMonoidalComp (η θ : Mor₂) (α : Structural) (η' θ' αθ ηαθ : NormalExpr)
    (e_η e_θ e_αθ e_ηαθ : Expr) : m Expr

variable {ρ : Type} [Context ρ]
variable [MonadMor₂Iso (CoherenceM ρ)] [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)]

open MkEvalComp MonadMor₂Iso MonadNormalExpr

/-- Evaluate the expression `α ≫ η` into a normalized form. -/
def evalCompNil (α : Structural) : NormalExpr → CoherenceM ρ Eval.Result
  | .nil _ β => do return ⟨← nilM (← comp₂M α β), ← mkEvalCompNilNil α β⟩
  | .cons _ β η ηs => do return ⟨← consM (← comp₂M α β) η ηs, ← mkEvalCompNilCons α β η ηs⟩

/-- Evaluate the expression `η ≫ θ` into a normalized form. -/
def evalComp : NormalExpr → NormalExpr → CoherenceM ρ Eval.Result
  | .nil _ α, η => do evalCompNil α η
  | .cons _ α η ηs, θ => do
    let ⟨ι, e_ι⟩ ← evalComp ηs θ
    return ⟨← consM α η ι, ← mkEvalCompCons α η ηs θ ι e_ι⟩

open MkEvalWhiskerLeft

variable [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso (CoherenceM ρ)]

/-- Evaluate the expression `f ◁ η` into a normalized form. -/
def evalWhiskerLeft : Mor₁ → NormalExpr → CoherenceM ρ Eval.Result
  | f, .nil _ α => do
    return ⟨← nilM (← whiskerLeftM f α), ← mkEvalWhiskerLeftNil f α⟩
  | .of f, .cons _ α η ηs => do
    let η' ← MonadWhiskerLeft.whiskerLeftM f η
    let ⟨θ, e_θ⟩ ← evalWhiskerLeft (.of f) ηs
    let η'' ← consM (← whiskerLeftM (.of f) α) η' θ
    return ⟨η'', ← mkEvalWhiskerLeftOfCons f α η ηs θ e_θ⟩
  | .comp _ f g, η => do
    let ⟨θ, e_θ⟩ ← evalWhiskerLeft g η
    let ⟨ι, e_ι⟩ ← evalWhiskerLeft f θ
    let h ← η.srcM
    let h' ← η.tgtM
    let ⟨ι', e_ι'⟩ ← evalComp ι (← NormalExpr.associatorInvM f g h')
    let ⟨ι'', e_ι''⟩ ← evalComp (← NormalExpr.associatorM f g h) ι'
    return ⟨ι'', ← mkEvalWhiskerLeftComp f g η θ ι ι' ι'' e_θ e_ι e_ι' e_ι''⟩
  | .id _ _, η => do
    let f ← η.srcM
    let g ← η.tgtM
    let ⟨η', e_η'⟩ ← evalComp η (← NormalExpr.leftUnitorInvM g)
    let ⟨η'', e_η''⟩ ← evalComp (← NormalExpr.leftUnitorM f) η'
    return ⟨η'', ← mkEvalWhiskerLeftId η η' η'' e_η' e_η''⟩

open MkEvalWhiskerRight MkEvalHorizontalComp

mutual

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightAux : HorizontalComp → Atom₁ → CoherenceM ρ Eval.Result
  | .of η, f => do
    let η' ← NormalExpr.ofM <| .of <| .of <| ← MonadWhiskerRight.whiskerRightM η f
    return ⟨η', ← mkEvalWhiskerRightAuxOf η f⟩
  | .cons _ η ηs, f => do
    let ⟨ηs', e_ηs'⟩ ← evalWhiskerRightAux ηs f
    let ⟨η₁, e_η₁⟩ ← evalHorizontalComp (← NormalExpr.ofM <| .of <| .of η) ηs'
    let ⟨η₂, e_η₂⟩ ← evalComp η₁ (← NormalExpr.associatorInvM (← η.tgtM) (← ηs.tgtM) (.of f))
    let ⟨η₃, e_η₃⟩ ← evalComp (← NormalExpr.associatorM (← η.srcM) (← ηs.srcM) (.of f)) η₂
    return ⟨η₃, ← mkEvalWhiskerRightAuxCons f η ηs ηs' η₁ η₂ η₃ e_ηs' e_η₁ e_η₂ e_η₃⟩

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRight : NormalExpr → Mor₁ → CoherenceM ρ Eval.Result
  | .nil _ α, h => do
    return ⟨← nilM (← whiskerRightM α h), ← mkEvalWhiskerRightNil α h⟩
  | .cons _ α (.of η) ηs, .of f => do
    let ⟨ηs₁, e_ηs₁⟩ ← evalWhiskerRight ηs (.of f)
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRightAux η f
    let ⟨η₂, e_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, e_η₃⟩ ← evalCompNil (← whiskerRightM α (.of f)) η₂
    return ⟨η₃, ← mkEvalWhiskerRightConsOfOf f α η ηs ηs₁ η₁ η₂ η₃ e_ηs₁ e_η₁ e_η₂ e_η₃⟩
  | .cons _ α (.whisker _ f η) ηs, h => do
    let g ← η.srcM
    let g' ← η.tgtM
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRight (← consM (← id₂M' g) η (← NormalExpr.idM g')) h
    let ⟨η₂, e_η₂⟩ ← evalWhiskerLeft (.of f) η₁
    let ⟨ηs₁, e_ηs₁⟩ ← evalWhiskerRight ηs h
    let α' ← whiskerRightM α h
    let ⟨ηs₂, e_ηs₂⟩ ← evalComp (← NormalExpr.associatorInvM (.of f) g' h) ηs₁
    let ⟨η₃, e_η₃⟩ ← evalComp η₂ ηs₂
    let ⟨η₄, e_η₄⟩ ← evalComp (← NormalExpr.associatorM (.of f) g h) η₃
    let ⟨η₅, e_η₅⟩ ← evalComp (← nilM α') η₄
    return ⟨η₅, ← mkEvalWhiskerRightConsWhisker f h α η ηs η₁ η₂ ηs₁ ηs₂ η₃ η₄ η₅
      e_η₁ e_η₂ e_ηs₁ e_ηs₂ e_η₃ e_η₄ e_η₅⟩
  | η, .comp _ g h => do
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRight η g
    let ⟨η₂, e_η₂⟩ ← evalWhiskerRight η₁ h
    let f ← η.srcM
    let f' ← η.tgtM
    let ⟨η₃, e_η₃⟩ ← evalComp η₂ (← NormalExpr.associatorM f' g h)
    let ⟨η₄, e_η₄⟩ ← evalComp (← NormalExpr.associatorInvM f g h) η₃
    return ⟨η₄, ← mkEvalWhiskerRightComp g h η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄⟩
  | η, .id _ _ => do
    let f ← η.srcM
    let g ← η.tgtM
    let ⟨η₁, e_η₁⟩ ← evalComp η (← NormalExpr.rightUnitorInvM g)
    let ⟨η₂, e_η₂⟩ ← evalComp (← NormalExpr.rightUnitorM f) η₁
    return ⟨η₂, ← mkEvalWhiskerRightId η η₁ η₂ e_η₁ e_η₂⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalHorizontalCompAux : HorizontalComp → HorizontalComp → CoherenceM ρ Eval.Result
  | .of η, θ => do
    return ⟨← NormalExpr.ofM <| .of <| ← MonadHorizontalComp.hConsM η θ,
      ← mkEvalHorizontalCompAuxOf η θ⟩
  | .cons _ η ηs, θ => do
    let α ← NormalExpr.associatorM (← η.srcM) (← ηs.srcM) (← θ.srcM)
    let α' ← NormalExpr.associatorInvM (← η.tgtM) (← ηs.tgtM) (← θ.tgtM)
    let ⟨ηθ, e_ηθ⟩ ← evalHorizontalCompAux ηs θ
    let ⟨η₁, e_η₁⟩ ← evalHorizontalComp (← NormalExpr.ofM <| .of <| .of η) ηθ
    let ⟨ηθ₁, e_ηθ₁⟩ ← evalComp η₁ α'
    let ⟨ηθ₂, e_ηθ₂⟩ ← evalComp α ηθ₁
    return ⟨ηθ₂, ← mkEvalHorizontalCompAuxCons η ηs θ ηθ η₁ ηθ₁ ηθ₂ e_ηθ e_η₁ e_ηθ₁ e_ηθ₂⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalHorizontalCompAux' : WhiskerLeft → WhiskerLeft → CoherenceM ρ Eval.Result
  | .of η, .of θ => evalHorizontalCompAux η θ
  | .whisker _ f η, θ => do
    let ⟨ηθ, e_ηθ⟩ ← evalHorizontalCompAux' η θ
    let ⟨ηθ₁, e_ηθ₁⟩ ← evalWhiskerLeft (.of f) ηθ
    let ⟨ηθ₂, e_ηθ₂⟩ ← evalComp ηθ₁ (← NormalExpr.associatorInvM (.of f) (← η.tgtM) (← θ.tgtM))
    let ⟨ηθ₃, e_ηθ₃⟩ ← evalComp (← NormalExpr.associatorM (.of f) (← η.srcM) (← θ.srcM)) ηθ₂
    return ⟨ηθ₃, ← mkEvalHorizontalCompAux'Whisker f η θ ηθ ηθ₁ ηθ₂ ηθ₃ e_ηθ e_ηθ₁ e_ηθ₂ e_ηθ₃⟩
  | .of η, .whisker _ f θ => do
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRightAux η f
    let ⟨ηθ, e_ηθ⟩ ← evalHorizontalComp η₁ (← NormalExpr.ofM θ)
    let ⟨ηθ₁, e_ηθ₁⟩ ← evalComp ηθ (← NormalExpr.associatorM (← η.tgtM) (.of f) (← θ.tgtM))
    let ⟨ηθ₂, e_ηθ₂⟩ ← evalComp (← NormalExpr.associatorInvM (← η.srcM) (.of f) (← θ.srcM)) ηθ₁
    return ⟨ηθ₂, ← mkEvalHorizontalCompAux'OfWhisker f η θ ηθ η₁ ηθ₁ ηθ₂ e_η₁ e_ηθ e_ηθ₁ e_ηθ₂⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalHorizontalComp : NormalExpr → NormalExpr → CoherenceM ρ Eval.Result
  | .nil _ α, .nil _ β => do
    return ⟨← nilM <| ← horizontalCompM α β, ← mkEvalHorizontalCompNilNil α β⟩
  | .nil _ α, .cons _ β η ηs => do
    let ⟨η₁, e_η₁⟩ ← evalWhiskerLeft (← α.tgtM) (← NormalExpr.ofM η)
    let ⟨ηs₁, e_ηs₁⟩ ← evalWhiskerLeft (← α.tgtM) ηs
    let ⟨η₂, e_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, e_η₃⟩ ← evalCompNil (← horizontalCompM α β) η₂
    return ⟨η₃, ← mkEvalHorizontalCompNilCons α β η ηs η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃⟩
  | .cons _ α η ηs, .nil _ β => do
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRight (← NormalExpr.ofM η) (← β.tgtM)
    let ⟨ηs₁, e_ηs₁⟩ ← evalWhiskerRight ηs (← β.tgtM)
    let ⟨η₂, e_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, e_η₃⟩ ← evalCompNil (← horizontalCompM α β) η₂
    return ⟨η₃, ← mkEvalHorizontalCompConsNil α β η ηs η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃⟩
  | .cons _ α η ηs, .cons _ β θ θs => do
    let ⟨ηθ, e_ηθ⟩ ← evalHorizontalCompAux' η θ
    let ⟨ηθs, e_ηθs⟩ ← evalHorizontalComp ηs θs
    let ⟨ηθ₁, e_ηθ₁⟩ ← evalComp ηθ ηθs
    let ⟨ηθ₂, e_ηθ₂⟩ ← evalCompNil (← horizontalCompM α β) ηθ₁
    return ⟨ηθ₂,
      ← mkEvalHorizontalCompConsCons α β η θ ηs θs ηθ ηθs ηθ₁ ηθ₂ e_ηθ e_ηθs e_ηθ₁ e_ηθ₂⟩

end

open MkEval

variable {ρ : Type} [Context ρ]
    [MonadMor₁ (CoherenceM ρ)]
    [MonadMor₂Iso (CoherenceM ρ)]
    [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)]
    [MonadMor₂ (CoherenceM ρ)]
    [MkMor₂ (CoherenceM ρ)]

/-- Trace the proof of the normalization. -/
def traceProof (nm : Name) (result : Expr) : CoherenceM ρ Unit := do
  withTraceNode nm (fun _ => return m!"{checkEmoji} {← inferType result}") do
    if ← isTracingEnabledFor nm then addTrace nm m!"proof: {result}"

-- TODO: It takes a while to compile. Find out why.
/-- Evaluate the expression of a 2-morphism into a normalized form. -/
def eval (nm : Name) (e : Mor₂) : CoherenceM ρ Eval.Result := do
  withTraceNode nm (fun _ => return m!"eval: {e.e}") do
    match e with
    | .isoHom _ _ α => withTraceNode nm (fun _ => return m!"Iso.hom") do match α with
      | .structuralAtom α => return ⟨← nilM <| .structuralAtom α, ← mkEqRefl e.e⟩
      | .of η =>
        let η ← MonadMor₂.atomHomM η
        let result ← mkEvalOf η
        traceProof nm result
        return ⟨← NormalExpr.ofAtomM η, result⟩
      | _ => throwError "not implemented. try dsimp first."
    | .isoInv _ _ α => withTraceNode nm (fun _ => return m!"Iso.inv") do match α with
      | .structuralAtom α => return ⟨← nilM <| (← symmM (.structuralAtom α)), ← mkEqRefl e.e⟩
      | .of η =>
        let η ← MonadMor₂.atomInvM η
        let result ← mkEvalOf η
        traceProof nm result
        return ⟨← NormalExpr.ofAtomM η, result⟩
      | _ => throwError "not implemented. try dsimp first."
    | .id _ _ f  =>
      let α ← MonadMor₂Iso.id₂M f
      return  ⟨← nilM <| .structuralAtom α, ← mkEqRefl e.e⟩
    | .comp _ _ _ _ _ η θ => withTraceNode nm (fun _ => return m!"comp") do
      let ⟨η', e_η⟩ ← eval nm η
      let ⟨θ', e_θ⟩ ← eval nm θ
      let ⟨ηθ, pf⟩ ← evalComp η' θ'
      let result ← mkEvalComp η θ η' θ' ηθ e_η e_θ pf
      traceProof nm result
      return ⟨ηθ, result⟩
    | .whiskerLeft _ _ f _ _ η => withTraceNode nm (fun _ => return m!"whiskerLeft") do
      let ⟨η', e_η⟩ ← eval nm η
      let ⟨θ, e_θ⟩ ← evalWhiskerLeft f η'
      let result ← mkEvalWhiskerLeft f η η' θ e_η e_θ
      traceProof nm result
      return ⟨θ, result⟩
    | .whiskerRight _ _ _ _ η h =>
      withTraceNode nm (fun _ => return m!"whiskerRight") do
        let ⟨η', e_η⟩ ← eval nm η
        let ⟨θ, e_θ⟩ ← evalWhiskerRight η' h
        let result ← mkEvalWhiskerRight η h η' θ e_η e_θ
        traceProof nm result
        return ⟨θ, result⟩
    | .coherenceComp _ _ _ _ _ _ α₀ η θ =>
      withTraceNode nm (fun _ => return m!"monoidalComp") do
        let ⟨η', e_η⟩ ← eval nm η
        let α₀ := .structuralAtom <| .coherenceHom α₀
        let α ← nilM α₀
        let ⟨θ', e_θ⟩ ← eval nm θ
        let ⟨αθ, e_αθ⟩ ← evalComp α θ'
        let ⟨ηαθ, e_ηαθ⟩ ← evalComp η' αθ
        let result ← mkEvalMonoidalComp η θ α₀ η' θ' αθ ηαθ e_η e_θ e_αθ e_ηαθ
        traceProof nm result
        return ⟨ηαθ, result⟩
    | .horizontalComp _ _ _ _ _ _ η θ =>
      withTraceNode nm (fun _ => return m!"horizontalComp") do
        let ⟨η', e_η⟩ ← eval nm η
        let ⟨θ', e_θ⟩ ← eval nm θ
        let ⟨ηθ, e_ηθ⟩ ← evalHorizontalComp η' θ'
        let result ← mkEvalHorizontalComp η θ η' θ' ηθ e_η e_θ e_ηθ
        traceProof nm result
        return ⟨ηθ, result⟩
    | .of η  =>
      let result ← mkEvalOf η
      traceProof nm result
      return ⟨← NormalExpr.ofAtomM η, result⟩

end

end Mathlib.Tactic.BicategoryLike
