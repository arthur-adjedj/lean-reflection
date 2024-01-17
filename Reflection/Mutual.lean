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

-- -- ! This fails:
-- gen_injective_theorems% Tmₛ

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
@TmₛA ["Nat -> Type"] "Type" "Vec 123" ⟨Vec, ()⟩
```
reduces to:
```
(@TmₛA ["Nat -> Type"] "Type" "Vec" ⟨Vec, ()⟩) 123
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
| .nil, _ => Unit
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
-- And for some reason TmₚD works just fine? What...
def TmₛD : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> {γₛ : ConₛA Γₛ} -> (t : Tmₛ  Γₛ Aₛ) -> ConₛD Γₛ γₛ -> TyₛD Aₛ (TmₛA t γₛ)
|  _, _, γₛ, .var v                    , γₛD => TmₛA_var.symm ▸ VarₛD v γₛD
| Γₛ, _, γₛ, .app (T := T) (A := A) t u, γₛD => TmₛA_app.symm ▸ TmₛD t γₛD u

theorem TmₛD_var : TmₛD (Tmₛ.var v) γₛD = TmₛA_var.symm ▸ VarₛD v γₛD := by rw [TmₛD]
theorem TmₛD_app : TmₛD (t @ u)     γₛD = TmₛA_app.symm ▸ TmₛD t γₛD u := by rw [TmₛD]

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
| El         Self, γD, self =>                                               TmₛD Self γD self
| PPi   T    Rest, γD, f    => (t : T) ->                                    TyₚD (Rest t) γD (f t)
| PFunc Self Rest, γD, f    => ⦃self : TmₛA Self γₛ⦄ -> TmₛD Self γD self -> TyₚD Rest γD (f self)

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
| .nil, _, _ => Unit
| .cons A Γ, γD, ⟨a, γ⟩ => TyₚD A γD a × ConₚD Γ γD γ

example {P : (n : Nat) -> Vec A n -> Type}
  : @ConₚD Vₛ ⟨Vec A, ⟨⟩⟩ (V_nil :: V_cons :: []) ⟨P, ⟨⟩⟩ ⟨Vec.nil, Vec.cons, ⟨⟩⟩
  = (
        (P 0 Vec.nil)
      × ((n : Nat) -> (a : A) -> (v : Vec A n) -> P n v -> P (n + 1) (Vec.cons n a v))
      × Unit
    )
  := rfl





-- ## Sections

/-- Example:
```
TyₛS (SPi Nat (fun _ => U)) (Vec A) (fun _ _ => R)
```
reduces to
```
(n : Nat) -> (v : Vec A n) -> R
``` -/
def TyₛS : (Aₛ : Tyₛ) -> (αₛ : TyₛA Aₛ) -> TyₛD Aₛ αₛ -> Type
| U       , T , TD  => (t : T) -> TD t
| SPi T Aₛ, fₛ, fₛd => (t : T) -> TyₛS (Aₛ t) (fₛ t) (fₛd t)

example {A R} : TyₛS (SPi Nat (fun _ => U)) (Vec A) (fun _ _ => R) = ((n : Nat) -> (v : Vec A n) -> R) := rfl

/-- Example:
```
ConₛS Vₛ ⟨Vec A, ⟨⟩⟩ ⟨fun _ _ => R, ⟨⟩⟩
```
reduces to
```
  ((n : Nat) -> (v : Vec A n) -> R)
× PUnit
``` -/
def ConₛS : (Γₛ : Conₛ) -> (γₛ : ConₛA Γₛ) -> ConₛD Γₛ γₛ -> Type
| .nil, ⟨⟩, ⟨⟩ => Unit
| .cons Aₛ Γₛ, ⟨αₛ, γₛ⟩, ⟨αₛd, γₛd⟩ => TyₛS Aₛ αₛ αₛd × ConₛS Γₛ γₛ γₛd

example {A R} : ConₛS Vₛ ⟨Vec A, ⟨⟩⟩ ⟨fun _ _ => R, ⟨⟩⟩ = (((n : Nat) -> (v : Vec A n) -> R) × Unit) := rfl

def VarₛS : (x : Varₛ Γₛ Aₛ) -> ConₛS Γₛ γₛ γD -> TyₛS Aₛ (VarₛA x γₛ) (VarₛD x γD)
| .vz  , ⟨αₛS, γₛS⟩ => αₛS
| .vs v, ⟨ _, γₛS⟩ => VarₛS v γₛS

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.28h.E2.82.82.20.E2.96.B8.20h.E2.82.81.29.20.E2.96.B8.20x.20.3D.20h.E2.82.82.20.E2.96.B8.20.28h.E2.82.81.20.E2.96.B8.20x.29/near/411362225 wow this URL
theorem eq_cast_trans  (h₁ : A = B) (h₂ : B = C) (x : A)
  : h₂ ▸ h₁ ▸ x = (h₂ ▸ h₁) ▸ x
  := by cases h₁; cases h₂; rfl

theorem eq_symm_cancel {T : I -> Type _} {a b : I} (h : a = b) (x : T b)
  : h ▸ h.symm ▸ x = x
  := by cases h; rfl

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/rw.20term.20depended.20on.20by.20other.20argument/near/409268800
theorem TyₛS_helper {Aₛ : Tyₛ} {a b : TyₛA Aₛ} (hA : a = b) (d : TyₛD Aₛ a)
  : TyₛS Aₛ a d = TyₛS Aₛ b (hA ▸ d)
  := by subst hA; rfl

-- set_option pp.notation false in
def TmₛS : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> {γₛ : ConₛA Γₛ} -> {γₛD : ConₛD Γₛ γₛ} ->
  (t : Tmₛ Γₛ Aₛ) -> ConₛS Γₛ γₛ γₛD -> TyₛS Aₛ (TmₛA t γₛ) (TmₛD t γₛD)
| Γₛ, Aₛ, γₛ, γₛD, .var v, γₛS => by
  have hA : TmₛA (Tmₛ.var v) γₛ = VarₛA v γₛ := TmₛA_var
  rw [TyₛS_helper hA (TmₛD (Tmₛ.var v) γₛD), TmₛD_var, eq_symm_cancel hA]
  exact VarₛS v γₛS
| Γₛ, _, γₛ, γₛD, .app (T := T) (A := Aₛ) t u, γₛS => by
  have hA : TmₛA (Tmₛ.app t u) γₛ = TmₛA t γₛ u := TmₛA_app
  rw [TyₛS_helper hA, TmₛD, eq_symm_cancel hA]
  exact TmₛS t γₛS u

def TyₚS : (A : Tyₚ Γₛ) -> ConₛS Γₛ γₛ γₛD -> (α : TyₚA A γₛ) -> TyₚD A γₛD α -> Prop
| El         Self, γₛS, α, αD =>                          TmₛS Self γₛS α = αD -- note the equality here!
| PPi   T    Rest, γₛS, f, fD => (t    : T)            -> TyₚS (Rest t) γₛS (f t)    (fD t)
| PFunc Self Rest, γₛS, f, fD => (self : TmₛA Self γₛ) ->
  -- fD : {self : TmₛA Self γₛ} → TmₛD Self γD self → TyₚD Rest γD (f self)
  TyₚS  Rest    γₛS (f self) (@fD self (TmₛS Self γₛS self))

def ConₚS : (Γ : Conₚ Γₛ) -> ConₛS Γₛ γₛ γₛD -> (γ : ConₚA Γ γₛ) -> ConₚD Γ γₛD γ -> Prop
| .nil     ,   _,     ⟨⟩,       ⟨⟩ => True
| .cons A Γ, γₛS, ⟨α, γ⟩, ⟨αD, γD⟩ => TyₚS A γₛS α αD ∧ ConₚS Γ γₛS γ γD

example : @ConₚS Vₛ ⟨Vec A, ⟨⟩⟩ ⟨Q, ⟨⟩⟩ (V A) ⟨f, ⟨⟩⟩ ⟨Vec.nil, Vec.cons, ⟨⟩⟩ ⟨nilD, consD, ⟨⟩⟩
  = (f 0 Vec.nil = nilD
    ∧ ((n : Nat) -> (a : A) -> (v : Vec A n) -> (f (n + 1) (Vec.cons n a v) = consD n a /- v -/ (f n v)))
    ∧ True)
  := rfl


-- # Substitutions

/-- Represents a substitution from Δₛ to Γₛ.
Note that `Subₛ` is essentially a list of the same length as the context `Δₛ`.
This is because for every entry in the context Δₛ we will substitute it
with a Γₛ-term saved in `Subₛ`, thus the resulting context will be Γₛ.  -/
inductive Subₛ : (Γₛ : Conₛ) -> (Δₛ : Conₛ) -> Type 1
| nil : Subₛ Γₛ .nil
| cons : Subₛ Γₛ Δₛ -> Tmₛ Γₛ Aₛ -> Subₛ Γₛ (Aₛ :: Δₛ)

/-- Substitutes a variable `v ∈ Δₛ` with a Γₛ-term. -/
def SubₛVar : Varₛ Δₛ Aₛ -> Subₛ Γₛ Δₛ -> Tmₛ Γₛ Aₛ
| .vz  , .cons _ t => t
| .vs v, .cons σ _ => SubₛVar v σ

/-- Applies the substitution to a term, resulting in a new term in the new context. -/
def SubₛTm : {Aₛ : _} -> Tmₛ Δₛ Aₛ -> Subₛ Γₛ Δₛ -> Tmₛ Γₛ Aₛ
| _, .var v, σ => SubₛVar v σ
| _, .app (A := _A) t u, σ => .app (SubₛTm t σ) u

def SubₛTy : Tyₚ Δₛ -> Subₛ Γₛ Δₛ -> Tyₚ Γₛ
| El Self, σ => El (SubₛTm Self σ)
| PPi T Rest, σ => PPi T (fun t => SubₛTy (Rest t) σ)
| PFunc Self Rest, σ => PFunc (SubₛTm Self σ) (SubₛTy Rest σ)

def SubₛCon : Conₚ Δₛ -> Subₛ Γₛ Δₛ -> Conₚ Γₛ
| [], _ => []
| A :: Γ, σ => SubₛTy A σ :: SubₛCon Γ σ

-- def weaken {Aₛ : Tyₛ} : Subₛ Γₛ Δₛ -> Subₛ (Aₛ :: Γₛ) Δₛ
-- | .nil => .nil
-- | .cons t σ => .cons (.vs t) (weaken σ)

def SubₛA : Subₛ Γₛ Δₛ -> ConₛA Γₛ -> ConₛA Δₛ
| .nil     ,  _ => ⟨⟩
| .cons σ t, γₛ => ⟨TmₛA t γₛ, SubₛA σ γₛ⟩

def SubₛD : (σ : Subₛ Γₛ Δₛ) -> ConₛD Γₛ γₛ -> ConₛD Δₛ (SubₛA σ γₛ)
| .nil, γₛD => ⟨⟩
| .cons σ t, γₛD => ⟨TmₛD t γₛD, SubₛD σ γₛD⟩

def SubₛS : (σ : Subₛ Γₛ Δₛ) -> ConₛS Γₛ γₛ γₛD -> ConₛS Δₛ (SubₛA σ γₛ) (SubₛD σ γₛD)
| .nil, γₛD => ⟨⟩
| .cons σ t, γₛD => ⟨TmₛS t γₛD, SubₛS σ γₛD⟩




-- ### Now for Points...

inductive Varₚ : Conₚ Γₛ -> Tyₚ Γₛ -> Type 1
| vz :               Varₚ (Aₛ :: Γₛ) Aₛ
| vs : Varₚ Γₛ Aₛ -> Varₚ (Bₛ :: Γₛ) Aₛ

#check PPi

set_option genInjectivity false in
inductive Tmₚ : Conₚ Γₛ -> Tyₚ Γₛ -> Type 1
| var : Varₚ Γ A -> Tmₚ Γ A
| app {T : Type} {A : T -> Tyₚ Γₛ} : Tmₚ Γ (PPi T A)   -> (t : T)      -> Tmₚ Γ (A t)
| appr           {A :      Tyₚ Γₛ} : Tmₚ Γ (PFunc a A) -> Tmₚ Γ (El a) -> Tmₚ Γ A

/-- Represents a substitution from Δₛ to Γₛ.
Note that `Subₛ` is essentially a list of the same length as the context `Δₛ`.
This is because for every entry in the context Δₛ we will substitute it
with a Γₛ-term saved in `Subₛ`, thus the resulting context will be Γₛ.  -/
inductive Subₚ : (Γ : Conₚ Γₛ) -> (Δ : Conₚ Δₛ) -> Type 1
| nil : Subₚ Γ .nil
| cons : Subₚ Γ Δ -> Tmₚ Γ A -> Subₚ Γ (A :: Δ)

/-- Substitutes a variable `v ∈ Δₛ` with a Γₛ-term. -/
def SubₚVar : Varₚ Δ A -> Subₚ Γ Δ -> Tmₚ Γ A
| .vz  , .cons _ t => t
| .vs v, .cons σ _ => SubₚVar v σ

/-- Applies the substitution to a term, resulting in a new term in the new context. -/
def SubₚTm : {A : Tyₚ Γₛ} -> Tmₚ Δ A -> Subₚ Γ Δ -> Tmₚ Γ A
| _, .var v, σ => SubₚVar v σ
| _, .app (A := _A) t u, σ => .app (SubₚTm t σ) u
| _, .appr (A := A) t u, σ => .appr (SubₚTm t σ) (SubₚTm u σ)

def VarₚA : Varₚ Γ A -> ConₚA Γ γₛ -> TyₚA A γₛ
| .vz  , ⟨a, _⟩ => a
| .vs v, ⟨_, γ⟩ => VarₚA v γ

def TmₚA : {A : Tyₚ Γₛ} -> Tmₚ Γ A -> ConₚA Γ γₛ -> TyₚA A γₛ
| _, .var v, γ => VarₚA v γ
| _, .app (A := _A) t u, γ => (TmₚA t γ) u
| _, .appr (A := _) t u, γ => (TmₚA t γ) (TmₚA u γ)

def SubₚA : Subₚ Γ Δ -> ConₚA Γ γₛ -> ConₚA Δ γₛ
| .nil     ,  _ => ⟨⟩
| .cons σ t, γₛ => ⟨TmₚA t γₛ, SubₚA σ γₛ⟩

def VarₚD : (x : Varₚ Γ A) -> ConₚD Γ γₛD γ -> TyₚD A γₛD (VarₚA x γ)
| .vz  , ⟨aD, _⟩ => aD
| .vs v, ⟨_, γD⟩ => VarₚD v γD

-- This works but TmₛA_var doesn't work by rfl?
@[simp] theorem TmₚA_var : TmₚA (Tmₚ.var v) γₛ = VarₚA v γₛ := by rfl

def TmₚD : (t : Tmₚ Γ A) -> ConₚD Γ γₛD γ -> TyₚD A γₛD (TmₚA t γ)
| .var v, γD => VarₚD v γD
| .app (A := _A) t u, γD => TmₚD t γD u
| .appr (A := A) t u, γD => TmₚD t γD (TmₚD u γD)

def SubₚD : (σ : Subₚ Γ Δ) -> ConₚD Γ γₛD γ -> ConₚD Δ γₛD (SubₚA σ γ)
| .nil, γD => ⟨⟩
| .cons σ t, γD => ⟨TmₚD t γD, SubₚD σ γD⟩

-- # Constructor

variable (Ωₛ : Conₛ)
variable (Ω : Conₚ Ωₛ)

#check TyₛA U
#reduce TyₛA U

-- def conₛTm' : {Aₛ : Tyₛ} -> Tmₛ Ωₛ Aₛ -> TyₛA Aₛ
-- | U, a => Tmₚ Ω (El a)
-- | SPi T Aₛ, t => sorry

-- def conₛ' : Subₛ Ωₛ Γₛ -> ConₛA Γₛ
-- | .nil => ⟨⟩
-- | .cons σ t => ⟨conₛ' t, conₛ' σ⟩
