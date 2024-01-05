import Lean -- not essential: only for `Lean.Meta.getEqnsFor?` later

/-
  Adaptation of https://dx.doi.org/10.4230/LIPIcs.FSCD.2020.23 for Lean4.
  Agda source for the above lives at https://bitbucket.org/javra/inductive-families
-/

set_option pp.proofs true

-- # Syntax

/-- Example for `Nat` is `U`, for `Vec` is `SPi Nat (fun n => U)`. -/
inductive Tyₛ : Type 1
| U : Tyₛ
| SPi : (T : Type) -> (T -> Tyₛ) -> Tyₛ
open Tyₛ

inductive Conₛ
| nil : Conₛ
| cons : Tyₛ -> Conₛ -> Conₛ
notation "[]" => Conₛ.nil
infixr:67 " :: " => Conₛ.cons

/-- De-brujin variable referring to an entry in the context.
A context is for example `["Even", "Odd"]`, then `.vz` refers to `"Even"`.
These are nameless, the quotations are only to ease explanation. -/
inductive Varₛ : Conₛ -> Tyₛ -> Type 1
| vz :               Varₛ (Aₛ :: Γₛ) Aₛ
| vs : Varₛ Γₛ Aₛ -> Varₛ (_  :: Γₛ) Aₛ
open Varₛ

set_option genInjectivity false in
/-- `t : Tmₛ Γ A` corresponds to `Γ ⊢ t : A`.
Original Agda: https://bitbucket.org/javra/inductive-families/src/717f404c220e17d0ac5917306fd74dd0c4883cde/agda/IF.agda#lines-25:27 -/
inductive Tmₛ : Conₛ -> Tyₛ -> Type 1
/-- A variable is a term.
```-
(a : A) ∈ Γ
-----------var
Γ ⊢ₛ a : A
``` -/
| var : Varₛ Γ A -> Tmₛ Γ A
/-- Function application.
```-
Γ ⊢ₛ f : (x : T) -> A x      arg : T
-------------------------------------app-Intro
Γ ⊢ₛ f arg : A arg
``` -/
| app : Tmₛ Γ (SPi T A) -> (arg : T) -> Tmₛ Γ (A arg)
infixl:50 " @ " => Tmₛ.app

-- ! This fails:
gen_injective_theorems% Tmₛ

/-- Constructor types `... -> Self ...`.

Example `"(n : Nat) -> A -> Vec n -> Vec (n + 1)"`:
```
def V_cons (A : Type) : Tyₚ Vₛ :=
  PPi Nat fun n => -- (n : Nat) ->
    PPi A fun _ => -- A ->
      PFunc ((Tmₛ.var vz) @ n) <| -- Vec n ->
        El ((Tmₛ.var vz) @ (n + 1)) -- Vec (n + 1)
```

The only way to create a `Tyₚ` is by ending it with a `El`, which must be a term in the universe `U`.
The only way to create a term like that is by using `Tmₛ.app` and `Tmₛ.var`.
For example the variables are `Even` and `Odd`, i.e. the other types in the mutual block being defined,
then `Even @ 123` is a term in universe `U`. -/
inductive Tyₚ : Conₛ -> Type 1
| El : Tmₛ Γₛ U -> Tyₚ Γₛ
| PPi   : (T : Type) -> (T -> Tyₚ Γₛ) -> Tyₚ Γₛ
/-- Allows us to introduce nested binders `(x : Self ...) -> ...`.
  `PFunc` is non-dependent, because it makes no sense to have `(self : Self ...) -> Self self`.
  (...but once you have ind-ind or ind-rec, it might be sensible?) -/
| PFunc : Tmₛ Γₛ U   ->       Tyₚ Γₛ  -> Tyₚ Γₛ
open Tyₚ

/-- List of constructor descriptions.

Example (natural numbers):
```
El (.var .vz) :: PFunc (.var .vz) (El (.var .vz)) :: []
```
Example (vectors):
```
V_nil :: V_cons A :: []
``` -/
inductive Conₚ : Conₛ -> Type 1
| nil : Conₚ Γ
| cons : Tyₚ Γ -> Conₚ Γ -> Conₚ Γ
notation "[]" => Conₚ.nil
infixr:67 " :: " => Conₚ.cons

section Examples
  /-- Corresponds to `Nat : U`. -/
  def Nₛ : Conₛ := U :: []
  /-- Corresponds to the two constructors `Nat.zero : Nat` and `Nat.succ : Nat -> Nat`. -/
  def N  : Conₚ Nₛ := El (.var .vz) :: PFunc (.var .vz) (El (.var .vz)) :: []

  -- Vec : Nat -> U
  def Vₛ : Conₛ := SPi Nat (fun _ => U) :: []

  -- Vec : Nat -> U   ⊢ₛ   Vec 0 : U
  def V_nil : Tyₚ Vₛ := El ((.var .vz) @ 0) -- Vec 0

  -- Vec : Nat -> U   ⊢ₛ   (n : Nat) -> A -> Vec n -> Vec (n + 1)
  def V_cons {A : Type} : Tyₚ Vₛ :=
    PPi Nat fun n => -- (n : Nat) ->
      PPi A fun _ => -- A ->
        PFunc ((Tmₛ.var vz) @ n) <| -- Vec n ->
          El ((Tmₛ.var vz) @ (n + 1)) -- Vec (n + 1)

  def V (A : Type) : Conₚ Vₛ := V_nil :: @V_cons A :: []
end Examples

-- # Semantics

/-- Interprets a sort type, for example `SPi Nat (fun n => U)` becomes `Nat -> Type`. -/
def TyₛA : Tyₛ -> Type 1
| U => Type
| SPi T A => (t : T) -> TyₛA (A t)

/-- Interprets a context of type formers.  The `Vec` example becomes `(Nat -> Type) × Unit`. -/
def ConₛA : Conₛ -> Type 1
| .nil => PUnit
| .cons A Γ => TyₛA A × ConₛA Γ

example : ConₛA Vₛ = ((Nat -> Type) × PUnit.{2}) := by rfl

/--
  Variable lookup. Given a context `Γₛ` and an interpretation `γₛ` for that context,
  we find the interpretation that we care about.
  Note that `γₛ` is a "list" with `List.cons` replaced with `Prod.mk`.

  For example if `Γₛ` is `["(n:Nat) -> U"]`, and if `γₛ` is `⟨Vec, ()⟩`,
  then `VarₛA vz γₛ` will reduce to `Vec`.

  This function returns an actual (unquoted) Lean type, e.g. `Vec`.
-/
def VarₛA : {Γₛ : Conₛ} -> Varₛ Γₛ Aₛ -> ConₛA Γₛ -> TyₛA Aₛ
| _Aₛ :: _Γₛ, vz  , ⟨a, _ ⟩ => a
| _   :: _Γₛ, vs v, ⟨_, γₛ⟩ => VarₛA v γₛ

/-- A `Vec` example in pseudocode, where quotation marks refer to object language:
```
TmₛA ["Nat -> Type"] "Type" "Vec 123" ⟨Vec, ()⟩
```
reduces to:
```
(TmₛA ["Nat -> Type"] "Type" "Vec" ⟨Vec, ()⟩) 123
```
reduces to:
```
Vec 123
```
The interesting thing here is that the quoted `"Vec"` is purely syntactic and doesn't use
the actual `Vec` at all, it is merely a de-Brujin index into the context, which is entirely nameless.
The purpose of `TmₛA` is to interpret the syntactic `"Vec 123"` into the actual `Vec 123`,
by giving it the actual `Vec` interpretation via the `γₛ : ConₛA Γₛ`

The [original Agda code](https://bitbucket.org/javra/inductive-families/src/717f404c220e17d0ac5917306fd74dd0c4883cde/agda/IFA.agda#lines-16:19)
for `TmₛA` is the following, although it has `VarₛA` inlined, hence 3 cases:
```agda
_ᵃt : ∀{ℓ Γc B} → TmS Γc B → _ᵃc {ℓ} Γc → _ᵃS {ℓ} B
(var vvz ᵃt)     (γ , α) = α
(var (vvs t) ᵃt) (γ , α) = (var t ᵃt) γ
((t $S α) ᵃt)    γ       = (t ᵃt) γ α
```
-/
def TmₛA : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> Tmₛ Γₛ Aₛ -> ConₛA Γₛ -> TyₛA Aₛ
| Γ, A, @Tmₛ.var _   _ v  , γₛ => VarₛA v γₛ
| Γ, _, @Tmₛ.app Γ T A t u, γₛ => (TmₛA t γₛ) u

-- ! Why doesn't `by rfl` work for these two? Because of this I have to use casts in TmₛD which then spreads all over the place.
@[simp] theorem TmₛA_var' : TmₛA (Tmₛ.var v) γₛ = VarₛA v γₛ := by rfl
@[simp] theorem TmₛA_var  : TmₛA (Tmₛ.var v) γₛ = VarₛA v γₛ := by rw [TmₛA]
@[simp] theorem TmₛA_app  : TmₛA (Tmₛ.app t u) γₛ = (TmₛA t γₛ) u := by rw [TmₛA]

example {Vec : Nat -> Type} : @TmₛA (SPi Nat (fun _ => U) :: []) U ((.var .vz) @ 123) ⟨Vec, ⟨⟩⟩ = Vec 123 := rfl

/-- Interprets a constructor type. See below for examples.  Example:
```
TyₚA (V_cons A) ⟨Vec, ⟨⟩⟩
```
reduces to the type of `Vec.cons` as you would expect:
```
(n : Nat) -> A -> Vec n -> Vec (n + 1)
``` -/
def TyₚA : Tyₚ Γₛ -> ConₛA Γₛ -> Type
| El    Self, γₛ => TmₛA Self γₛ
| PPi   T    Rest, γₛ => (arg : T)    -> TyₚA (Rest arg) γₛ
| PFunc Self Rest, γₛ => TmₛA Self γₛ -> TyₚA Rest γₛ

example {Vec : Nat -> Type} {_A : Type}
  : TyₚA V_nil ⟨Vec, ⟨⟩⟩
  = Vec 0
  := rfl

example {Vec : Nat -> Type} {A : Type}
  : TyₚA (@V_cons A) ⟨Vec, ⟨⟩⟩
  = ((n : Nat) -> A -> Vec n -> Vec (n + 1))
  := rfl

/-- Interprets a (mutual) inductive type. This is just `TyₚA` for each ctor joined with `×`.
Example:
```
ConₚA (V_nil :: V_cons A :: []) ⟨Vec, ⟨⟩⟩
```
reduces to the Lean type
```
  (Vec 0) -- `Vec.nil`
× ((n : Nat) -> A -> Vec n -> Vec (n + 1)) -- `Vec.cons`
× Unit
``` -/
def ConₚA : Conₚ Γₛ -> ConₛA Γₛ -> Type
| .nil, _ => PUnit
| .cons A Γ, γₛ => TyₚA A γₛ × ConₚA Γ γₛ

example {Vec : Nat -> Type} {A : Type}
  : ConₚA (V A) ⟨Vec, ⟨⟩⟩
  = ((Vec 0) × ((n : Nat) -> A -> Vec n -> Vec (n + 1)) × Unit)
  := rfl

-- ## Displayed Algebras

/-- Compute motive type.

Example: `TyₛD (SPi Nat (fun _ => U)) Vec` reduces to `(n : Nat) -> Vec n -> Type`. -/
def TyₛD : (Aₛ : Tyₛ) -> TyₛA Aₛ -> Type 1
| U, T => T -> Type
| SPi T Aₛ, f => (t : T) -> TyₛD (Aₛ t) (f t)

/-- Compute motive type for each mutually defined inductive type.

Example:
```
ConₛD Vₛ ⟨Vec, ⟨⟩⟩
```
reduces to just one motive type:
```
((t : Nat) → Vec t -> Type) × Unit
``` -/
def ConₛD : (Γₛ : Conₛ) -> ConₛA Γₛ -> Type 1
| .nil, _ => PUnit
| .cons A Γ, ⟨a, γ⟩ => TyₛD A a × ConₛD Γ γ

example {Vec : Nat -> Type} : ConₛD Vₛ ⟨Vec, ⟨⟩⟩ = (((t : Nat) → Vec t -> Type) × PUnit.{2}) := rfl

def VarₛD : (v : Varₛ Γₛ Aₛ) -> ConₛD Γₛ γₛ -> TyₛD Aₛ (VarₛA v γₛ)
| .vz  , ⟨a, _⟩ => a
| .vs v, ⟨a, γD⟩ => VarₛD v γD

/--
The [original Agda code](https://bitbucket.org/javra/inductive-families/src/717f404c220e17d0ac5917306fd74dd0c4883cde/agda/IFD.agda#lines-17:20)
for this is, again with `VarₛD` inlined:
```agda
ᵈt : ∀{ℓ' ℓ Γc B}(t : TmS Γc B){γc : _ᵃc {ℓ} Γc} → ᵈc {ℓ'} Γc γc → ᵈS {ℓ'} B ((t ᵃt) γc)
ᵈt (var vvz)     (γcᵈ , αᵈ) = αᵈ
ᵈt (var (vvs t)) (γcᵈ , αᵈ) = ᵈt (var t) γcᵈ
ᵈt (t $S α)      γcᵈ        = ᵈt t γcᵈ α
``` -/
-- ! TmₛD needs casts because reduction behaviour of TmₛA is broken.
def TmₛD : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> {γₛ : ConₛA Γₛ} -> (t : Tmₛ  Γₛ Aₛ) -> ConₛD Γₛ γₛ -> TyₛD Aₛ (TmₛA t γₛ)
| A :: Γₛ, _, γₛ, .var v                    , γD => TmₛA_var ▸ VarₛD v γD
|      Γₛ, _, γₛ, .app (T := T) (A := A) t u, γD => TmₛA_app ▸ TmₛD t γD u

#eval Lean.Meta.getEqnsFor? ``TmₛA -- Works just fine.
#eval Lean.Meta.getEqnsFor? ``TmₛD -- ! TmₛD fails to generate equation theorems.

-- Manually proving equation theorems (.var, then .app) for TmₛD:
theorem TmₛD_var {v : Varₛ Γₛ Aₛ} {γₛD : ConₛD Γₛ γₛ} : TmₛD (Tmₛ.var v) γₛD = TmₛA_var ▸ VarₛD v γₛD := by
  unfold TmₛD
  cases Γₛ with
  | nil => sorry -- I give up.
  | cons => simp

/-- Example:
```
@TyₚD Vₛ ⟨Vec A, ⟨⟩⟩ V_nil ⟨P, ⟨⟩⟩ Vec.nil
  = P 0 Vec.nil
```
Example:
```
@TyₚD Vₛ ⟨Vec A, ⟨⟩⟩ V_cons ⟨P, ⟨⟩⟩ Vec.cons
  = ((n : Nat) -> (a : A) -> (v : Vec A n) -> P n v -> P (n + 1) (Vec.cons n a v))
``` -/
-- Note: The `Self` here can be a little misleading, as it may be a nested type with different indices.
def TyₚD : (A : Tyₚ Γₛ) -> ConₛD Γₛ γₛ -> TyₚA A γₛ -> Type
| El         Self, γD, self => TmₛD Self γD self
| PPi   T    Rest, γD, f    => (t : T) -> TyₚD (Rest t) γD (f t)
| PFunc Self Rest, γD, f    => (self : TmₛA Self γₛ) -> TmₛD Self γD self -> TyₚD Rest γD (f self)

inductive Vec (A : Type) : Nat -> Type
| nil : Vec A 0
| cons : (n : Nat) -> A -> Vec A n -> Vec A (n + 1)

example {A : Type} {P : (n : Nat) -> Vec A n -> Type}
  : @TyₚD Vₛ ⟨Vec A, ⟨⟩⟩ V_nil ⟨P, ⟨⟩⟩ Vec.nil
  = P 0 Vec.nil
  := rfl
example {A : Type} {P : (n : Nat) -> Vec A n -> Type}
  : @TyₚD Vₛ ⟨Vec A, ⟨⟩⟩ V_cons ⟨P, ⟨⟩⟩ Vec.cons
  = ((n : Nat) -> (a : A) -> (v : Vec A n) -> P n v -> P (n + 1) (Vec.cons n a v))
  := rfl

/-- Example:
```
@ConₚD Vₛ ⟨Vec A, ⟨⟩⟩ (V_nil :: V_cons :: []) ⟨P, ⟨⟩⟩ ⟨Vec.nil, Vec.cons, ⟨⟩⟩
```
reduces to
```
  P 0 Vec.nil
× ((n : Nat) -> (a : A) -> (v : Vec A n) -> P n v -> P (n + 1) (Vec.cons n a v))
× PUnit
``` -/
def ConₚD : (Γ : Conₚ Γₛ) -> ConₛD Γₛ γₛ -> ConₚA Γ γₛ -> Type
| .nil, _, _ => PUnit
| .cons A Γ, γD, ⟨a, γ⟩ => TyₚD A γD a × ConₚD Γ γD γ

example {P : (n : Nat) -> Vec A n -> Type}
  : @ConₚD Vₛ ⟨Vec A, ⟨⟩⟩ (V_nil :: V_cons :: []) ⟨P, ⟨⟩⟩ ⟨Vec.nil, Vec.cons, ⟨⟩⟩
  = (
        (P 0 Vec.nil)
      × ((n : Nat) -> (a : A) -> (v : Vec A n) -> P n v -> P (n + 1) (Vec.cons n a v))
      × PUnit
    )
  := rfl

-- ## Sections

def TyₛS : (Aₛ : Tyₛ) -> (αₛ : TyₛA Aₛ) -> TyₛD Aₛ αₛ -> Type
| U       , T , TD  => (t : T) -> TD t
| SPi T Aₛ, fₛ, fₛd => (t : T) -> TyₛS (Aₛ t) (fₛ t) (fₛd t)

def ConₛS : (Γₛ : Conₛ) -> (γₛ : ConₛA Γₛ) -> ConₛD Γₛ γₛ -> Type
| .nil, ⟨⟩, ⟨⟩ => PUnit
| .cons Aₛ Γₛ, ⟨αₛ, γₛ⟩, ⟨αₛd, γₛd⟩ => TyₛS Aₛ αₛ αₛd × ConₛS Γₛ γₛ γₛd

def VarₛS : (x : Varₛ Γₛ Aₛ) -> ConₛS Γₛ γₛ γD -> TyₛS Aₛ (VarₛA x γₛ) (VarₛD x γD)
| .vz  , ⟨αₛS, γₛS⟩ => αₛS
| .vs v, ⟨ _, γₛS⟩ => VarₛS v γₛS

theorem eq_cast_trans (h₁ : A = B) (h₂ : B = C) (x : A) : h₂ ▸ h₁ ▸ x = (h₂ ▸ h₁) ▸ x := by cases h₁; cases h₂; rfl -- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.28h.E2.82.82.20.E2.96.B8.20h.E2.82.81.29.20.E2.96.B8.20x.20.3D.20h.E2.82.82.20.E2.96.B8.20.28h.E2.82.81.20.E2.96.B8.20x.29/near/411362225 wow this URL
@[simp] theorem eq_symm_cancel (T : B) (h : A = B) : h ▸ h.symm ▸ T = T := by rw [eq_cast_trans]

-- set_option pp.notation false in
def TmₛS  : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> {γₛ : ConₛA Γₛ} -> {γₛD : ConₛD Γₛ γₛ} -> (t : Tmₛ  Γₛ Aₛ) -> ConₛS Γₛ γₛ γₛD -> TyₛS Aₛ (TmₛA t γₛ) (TmₛD t γₛD)
| Γₛ, Aₛ, γₛ, γₛD, .var v, γₛS => by
  have hA : TmₛA (Tmₛ.var v) γₛ  =            VarₛA v γₛ  := @TmₛA_var Γₛ Aₛ v γₛ
  have hD : TmₛD (Tmₛ.var v) γₛD = hA.symm ▸ VarₛD v γₛD := by rw [TmₛD_var] -- this should work by rfl

  -- Kyle's trick from a different thread: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/rw.20term.20depended.20on.20by.20other.20argument/near/409268800
  have {a b : TyₛA Aₛ} (hA : a = b) (d : TyₛD Aₛ a)
    : TyₛS Aₛ a d
    = TyₛS Aₛ b (hA ▸ d)
    := by subst hA; rfl

  rw [this hA (TmₛD (Tmₛ.var v) γₛD)]
  rw [hD]
  -- exact VarₛS v γₛS -- need to use eq_cast_trans here
  sorry
| _, _, _asdf, γD, .app (A := A) t u, γₛ => by
  sorry

def TyₚS  : (A : Tyₚ Γₛ) -> ConₛS Γₛ γₛ γD -> (α : TyₚA A γₛ) -> TyₚD A γD α -> Type := sorry

def ConₚS : (Γ : Conₚ Γₛ) -> ConₛS Γₛ γₛ γD -> (γ : ConₚA Γ γₛ) -> ConₚD Γ γD γ -> Type := sorry
