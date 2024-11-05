import Lean -- not essential: only for `Lean.Meta.getEqnsFor?` later
import Reflection.Util.EqHelpers


/-
  Adaptation of https://dx.doi.org/10.4230/LIPIcs.FSCD.2020.23 for Lean4.
  Agda source for the above lives at https://bitbucket.org/javra/inductive-families
-/

set_option pp.proofs true
set_option pp.universes true
set_option linter.unusedVariables false

/--Direction of a parameter, describes whether it
is used in an invariant way `none`, covariant `leq`, contravariant `geq` of equivariant `eq`.
Currently unused.-/
inductive Dir where
  | none
  | leq
  | geq
  | eq

-- # Syntax

/-- Example for `Nat` is `@U []`, for `List` is `@U [leq]`. -/
inductive Tyₛ (l : List Dir): Type u
| U : Tyₛ l
-- No need to work on indexed inductives just yet, let's focus on polymorphic types first
-- | SArr : (T : Type u) -> Tyₛ -> Tyₛ
open Tyₛ

inductive Conₛ (l : List Dir)
| nil : Conₛ l
| cons : Tyₛ l -> Conₛ l -> Conₛ l
notation "[]" => Conₛ.nil
infixr:67 " :: " => Conₛ.cons

/-- De-brujin variable referring to an entry in the context.
A context is for example `["Even", "Odd"]`, then `.vz` refers to `"Even"`.
These are nameless, the quotations are only to ease explanation. -/
inductive Varₛ : Conₛ l -> Tyₛ l -> Type u
| vz :               Varₛ (Aₛ :: Γₛ) Aₛ
| vs : Varₛ Γₛ Aₛ -> Varₛ (Bₛ :: Γₛ) Aₛ
open Varₛ

inductive Varₚ : List Dir → Type (u+1)
| vz : Varₚ [A]
| vs : Varₚ l -> Varₚ (Bₛ :: l)

/-- `t : Tmₛ Γ A` corresponds to `Γ ⊢ t : A`.
Original Agda: https://bitbucket.org/javra/inductive-families/src/717f404c220e17d0ac5917306fd74dd0c4883cde/agda/IF.agda#lines-25:27 -/
inductive Tmₛ.{u} : Conₛ.{u} l -> Tyₛ.{u} l -> Type (u+1)
/-- A variable is a term.
```-
(a : A) ∈ Γ
-----------varInd
Γ ⊢ₛ a : A
``` -/
| varInd : Varₛ Γ A -> Tmₛ Γ A
/-- Function application.
```-
A ∈ l
-----------varParam
Γ ⊢ₛ A : Type
``` -/
| varParam : Varₚ l → Tmₛ Γ (@U l)
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
inductive Tyₚ : Conₛ l -> Type (u+1)
| El : Tmₛ.{u} Γₛ U -> Tyₚ Γₛ
-- No need to work with dependent types just yet.
| PArr   : (T : Type u) -> Tyₚ Γₛ -> Tyₚ Γₛ
/-- Allows us to introduce nested binders `(x : Self ...) -> ...`.
  `PFunc` is non-dependent, because it makes no sense to have `(self : Self ...) -> Self self`.
  (...but once you have ind-ind or ind-rec, it might be sensible?) -/
| PFunc : Tmₛ Γₛ U   -> Tyₚ Γₛ  -> Tyₚ Γₛ
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
inductive Conₚ (Γ : Conₛ l): Type (u+1)
| nil : Conₚ Γ
| cons : Tyₚ Γ -> Conₚ Γ -> Conₚ Γ
notation "[]" => Conₚ.nil
infixr:67 " :: " => Conₚ.cons

section Examples
  /-- Corresponds to `Nat : U`. -/
  def Nₛ : Conₛ .nil := U :: []
  /-- Corresponds to the two constructors `Nat.zero : Nat` and `Nat.succ : Nat -> Nat`. -/
  def N  : Conₚ Nₛ := El (.varInd .vz) :: PFunc (.varInd .vz) (El (.varInd .vz)) :: []

  -- List : Type → U
  def Vₛ : Conₛ [.none] := U :: []

  -- List : Type → U ⊢ₛ  List A : U
  def V_nil : Tyₚ Vₛ := El (.varInd .vz) -- List A

  -- List : Type → U ⊢ₛ  A → List A → List A
  def V_cons : Tyₚ Vₛ :=
    PFunc (Tmₛ.varParam .vz) <| -- A →
      PFunc (Tmₛ.varInd vz) <| -- List A ->
        El (Tmₛ.varInd vz) -- List A

  def V : Conₚ Vₛ := V_nil :: V_cons :: []
end Examples

-- # Semantics

/-- The type of Parameter Telescopes. `l.Telescope` is a monad, which makes constructions over it useful. -/
def List.Telescope (l : List Dir) (A : Type (u+1)) := l.foldr (fun T₁ T₂ => Type u → T₂) A

def List.Telescope.pure (l : List Dir) (x : A) : List.Telescope l A :=
  match l with
    | .nil => x
    | .cons hd tl => fun _ : Type _ => List.Telescope.pure tl x
--
def List.Telescope.bind (l : List Dir) (x : List.Telescope l A) (f : A → List.Telescope l B)
: List.Telescope l B :=
  match l with
    | .nil => f x
    | .cons hd tl => fun h : Type _ => List.Telescope.bind tl (x h) (fun y => f y h)

instance : Monad (List.Telescope l) where
  pure := List.Telescope.pure l
  bind := List.Telescope.bind l

/-- Interprets a sort type, for example `SPi Nat (fun n => U)` becomes `Nat -> Type`. -/
def TyₛA : Tyₛ.{u} l -> Type (u+1) := fun _ => (Type u)
-- | SPi T A => (t : T) -> TyₛA (A t)

/-- Interprets a context of type formers.  The `Vec` example becomes `(Nat -> Type) × Unit`. -/
def ConₛA' : Conₛ l -> Type (u+1)
  | .nil => PUnit
  | .cons A Γ => Prod (TyₛA A) (ConₛA' Γ)
termination_by structural Γₛ => Γₛ

def ConₛA (Γₛ : Conₛ l): Type (u+1) := l.Telescope (ConₛA' Γₛ)

example : ConₛA Vₛ = (Type → (Type × PUnit.{2})) := by rfl

/--
  Variable lookup. Given a context `Γₛ` and an interpretation `γₛ` for that context,
  we find the interpretation that we care about.
  Note that `γₛ` is a "list" with `List.cons` replaced with `Prod.mk`.

  For example if `Γₛ` is `["(n:Nat) -> U"]`, and if `γₛ` is `⟨Vec, ()⟩`,
  then `VarₛA vz γₛ` will reduce to `Vec`.

  This function returns an actual (unquoted) Lean type, e.g. `Vec`.
-/
def VarₛA {Γₛ : Conₛ l} (v : Varₛ Γₛ Aₛ) (c : ConₛA Γₛ): l.Telescope (TyₛA Aₛ) := do
  let c ← c
  match v, c with
    |  vz  , ⟨a, _ ⟩ => pure a
    |  vs v, ⟨_, γₛ⟩ => VarₛA v (pure γₛ)


def VarₚA : {l : List Dir} → Varₚ l -> l.Telescope (Type u)
|  [d], .vz  => fun A => A
| _   :: l, .vs v => fun _ => VarₚA v

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
def TmₛA.{u} {Γₛ : Conₛ.{u} l} {Aₛ : Tyₛ l} (t : Tmₛ Γₛ Aₛ) ( γₛ : ConₛA Γₛ): l.Telescope (TyₛA Aₛ) :=
match t with
  | Tmₛ.varInd   v => VarₛA v γₛ
  | Tmₛ.varParam v => VarₚA v

@[simp] theorem TmₛA_var  : TmₛA (Tmₛ.varInd v) γₛ = VarₛA v γₛ := by rw [TmₛA]
-- @[simp] theorem TmₛA_app  : TmₛA (Tmₛ.app t u) γₛ = (TmₛA t γₛ) u := by rw [TmₛA]

example {List : Type → Type} : @TmₛA [.eq] (U :: []) U (.varInd .vz) (fun A => ⟨List A, ⟨⟩⟩) = List := rfl

/-- Interprets a constructor type. See below for examples.  Example:
```
TyₚA (V_cons A) ⟨Vec, ⟨⟩⟩
```
reduces to the type of `Vec.cons` as you would expect:
```
(n : Nat) -> A -> Vec n -> Vec (n + 1)
``` -/
def TyₚA.{u} {Γₛ : Conₛ.{u} l} (t : Tyₚ.{u} Γₛ) (γₛ : ConₛA.{u} Γₛ): l.Telescope (Type u) :=
match t with
| El Self => TmₛA.{u} Self γₛ
| PArr T Rest => do
  let h ← TyₚA Rest γₛ
  return T → h
| PFunc Self Rest => do
  let hd ← TmₛA Self γₛ
  let h ← TyₚA Rest γₛ
  return hd → h

example {List : Type → Type}
  : TyₚA V_nil (fun A => ⟨List A, ⟨⟩⟩)
  = List
  := rfl

set_option pp.universes false in
example {List : Type → Type }
  : TyₚA (V_cons) (fun A => ⟨List A, ⟨⟩⟩)
  = fun A => A → List A → List A
  := rfl

-- #exit

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
def ConₚA.{u} {Γₛ : Conₛ.{u} l} : Conₚ.{u} Γₛ -> ConₛA.{u} Γₛ -> l.Telescope (Type u)
| .nil, _ => pure PUnit.{u+1}
| .cons A Γ, γₛ => do
  let t₁ ← TyₚA.{u} A γₛ
  let t₂ ← ConₚA Γ γₛ
  return t₁ ×  t₂

example {List : Type → Type} {A : type}
  : ConₚA V (fun A => ⟨List A, ⟨⟩⟩)
  = fun A => (List A × (A -> List A -> List A) × Unit)
  := rfl

-- ## Displayed Algebras

/-- Compute motive type.

Example: `TyₛD (SPi Nat (fun _ => U)) Vec` reduces to `(n : Nat) -> Vec n -> Type`. -/
def TyₛD.{u} (Aₛ : Tyₛ.{u} l) : TyₛA.{u} Aₛ -> Type u :=
  fun T => T -> Sort u
-- | SPi T Aₛ, f => (t : T) -> TyₛD (Aₛ t) (f t)

/-- Compute motive type for each mutually defined inductive type.

Example:
```
ConₛD Vₛ ⟨Vec, ⟨⟩⟩
```
reduces to just one motive type:
```
((t : Nat) → Vec t -> Type) × Unit
``` -/
def ConₛD.{u} (Γₛ : Conₛ.{u} l) (c : ConₛA.{u} Γₛ): l.Telescope (Type u) :=
match Γₛ with
| .nil => return PUnit
| .cons A Γ => do
  let ⟨a,γ⟩ ← c
  return (TyₛD A a) × (← ConₛD Γ (pure γ))

example : ConₛD Vₛ (fun A => ⟨List A, ⟨⟩⟩) = fun A : Type => ((List A -> Prop) × PUnit.{1}) := rfl

def VarₛD {Γₛ : Conₛ.{u} l}: (v : Varₛ Γₛ Aₛ) -> ConₛD Γₛ γₛ -> TyₛD Aₛ (VarₛA v γₛ)
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
|  _, _, _γₛ, .var v                    , γₛD => TmₛA_var.symm ▸ VarₛD v γₛD
-- | Γₛ, _, γₛ, .app (T := T) (A := A) t u, γₛD => TmₛA_app.symm ▸ TmₛD t γₛD u

theorem TmₛD_var : TmₛD (Tmₛ.var v) γₛD = TmₛA_var.symm ▸ VarₛD v γₛD := by rw [TmₛD]
-- theorem TmₛD_app : TmₛD (t @ u)     γₛD = TmₛA_app.symm ▸ TmₛD t γₛD u := by rw [TmₛD]

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
def TyₚD.{u, v} : (A : Tyₚ.{u} Γₛ) -> ConₛD.{u} Γₛ γₛ -> TyₚA.{u, v} A γₛ -> Type (max u v)
| El         Self, γD, self => TmₛD Self γD self
| PArr   T    Rest, γD, f   => (t : T) -> TyₚD Rest γD (f t)
| PFunc Self Rest, γD, f    => ⦃self : TmₛA Self γₛ⦄ -> TmₛD Self γD self -> TyₚD Rest γD (f self)

inductive Vec (A : Type) : Nat -> Type
| nil : Vec A 0
| cons : (n : Nat) -> A -> Vec A n -> Vec A (n + 1)

example {A : Type} {P : List A -> Type}
  : @TyₚD Vₛ ⟨List A, ⟨⟩⟩ V_nil ⟨P, ⟨⟩⟩ List.nil
  = P List.nil
  := rfl
example {A : Type} {P : List A -> Type}
  : @TyₚD Vₛ ⟨List A, ⟨⟩⟩ V_cons ⟨P, ⟨⟩⟩ List.cons
  = ((a : A) -> (v : List A) -> P v -> P (List.cons a v))
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
def ConₚD.{u, v} : (Γ : Conₚ.{u} Γₛ) -> ConₛD.{u, v} Γₛ γₛ -> ConₚA.{u, v} Γ γₛ -> Type (max u v)
| .nil, _, _ => PUnit
| .cons A Γ, γD, ⟨a, γ⟩ => TyₚD A γD a × ConₚD Γ γD γ

example {P : List A -> Type}
  : @ConₚD Vₛ ⟨List A, ⟨⟩⟩ (V_nil :: V_cons :: []) ⟨P, ⟨⟩⟩ ⟨List.nil, List.cons, ⟨⟩⟩
  = (
        (P List.nil)
      × ((a : A) -> (v : List A) -> P v -> P (List.cons a v))
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
def TyₛS.{u, v} : (Aₛ : Tyₛ.{u}) -> (αₛ : TyₛA.{u, v} Aₛ) -> TyₛD.{u, v} Aₛ αₛ -> Type (max u v)
| U       , T , TD  => (t : T) -> TD t
-- | SPi T Aₛ, fₛ, fₛd => (t : T) -> TyₛS (Aₛ t) (fₛ t) (fₛd t)

-- example {A R} : TyₛS (SPi Nat (fun _ => U)) (Vec A) (fun _ _ => R) = ((n : Nat) -> (v : Vec A n) -> R) := rfl

/-- Example:
```
ConₛS Vₛ ⟨Vec A, ⟨⟩⟩ ⟨fun _ _ => R, ⟨⟩⟩
```
reduces to
```
  ((n : Nat) -> (v : Vec A n) -> R)
× PUnit
``` -/
def ConₛS.{u, v} : (Γₛ : Conₛ.{u}) -> (γₛ : ConₛA.{u, v} Γₛ) -> ConₛD.{u, v} Γₛ γₛ -> Type (max u v)
| .nil, ⟨⟩, ⟨⟩ => PUnit
| .cons Aₛ Γₛ, ⟨αₛ, γₛ⟩, ⟨αₛd, γₛd⟩ => TyₛS Aₛ αₛ αₛd × ConₛS Γₛ γₛ γₛd

-- example {A R} : ConₛS Vₛ ⟨Vec A, ⟨⟩⟩ ⟨fun _ _ => R, ⟨⟩⟩ = (((n : Nat) -> (v : Vec A n) -> R) × Unit) := rfl

def VarₛS : (x : Varₛ Γₛ Aₛ) -> ConₛS Γₛ γₛ γD -> TyₛS Aₛ (VarₛA x γₛ) (VarₛD x γD)
| .vz  , ⟨αₛS, γₛS⟩ => αₛS
| .vs v, ⟨ _, γₛS⟩ => VarₛS v γₛS

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/rw.20term.20depended.20on.20by.20other.20argument/near/409268800
theorem TyₛS_helper {Aₛ : Tyₛ} {a b : TyₛA Aₛ} (hA : a = b) (d : TyₛD Aₛ a)
  : TyₛS Aₛ a d = TyₛS Aₛ b (hA ▸ d)
  := by subst hA; rfl

def TmₛS : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> {γₛ : ConₛA Γₛ} -> {γₛD : ConₛD Γₛ γₛ} ->
  (t : Tmₛ Γₛ Aₛ) -> ConₛS Γₛ γₛ γₛD -> TyₛS Aₛ (TmₛA t γₛ) (TmₛD t γₛD)
| Γₛ, Aₛ, γₛ, γₛD, .var v, γₛS => by
  have hA : TmₛA (Tmₛ.var v) γₛ = VarₛA v γₛ := TmₛA_var
  rw [TyₛS_helper hA (TmₛD (Tmₛ.var v) γₛD), TmₛD_var, eq_symm_cancel hA]
  exact VarₛS v γₛS

def TyₚS : (A : Tyₚ Γₛ) -> ConₛS Γₛ γₛ γₛD -> (α : TyₚA A γₛ) -> TyₚD A γₛD α -> Prop
| El         Self, γₛS, α, αD =>                          TmₛS Self γₛS α = αD -- note the equality here!
| PArr   T    Rest, γₛS, f, fD => (t    : T)         -> TyₚS Rest γₛS (f t)    (fD t)
| PFunc Self Rest, γₛS, f, fD => (self : TmₛA Self γₛ) ->
  -- fD : {self : TmₛA Self γₛ} → TmₛD Self γD self → TyₚD Rest γD (f self)
  TyₚS  Rest    γₛS (f self) (@fD self (TmₛS Self γₛS self))

def ConₚS : (Γ : Conₚ Γₛ) -> ConₛS Γₛ γₛ γₛD -> (γ : ConₚA Γ γₛ) -> ConₚD Γ γₛD γ -> Prop
| .nil     ,   _,     ⟨⟩,       ⟨⟩ => True
| .cons A Γ, γₛS, ⟨α, γ⟩, ⟨αD, γD⟩ => TyₚS A γₛS α αD ∧ ConₚS Γ γₛS γ γD

-- example : @ConₚS Vₛ ⟨Vec A, ⟨⟩⟩ ⟨Q, ⟨⟩⟩ (V A) ⟨f, ⟨⟩⟩ ⟨Vec.nil, Vec.cons, ⟨⟩⟩ ⟨nilD, consD, ⟨⟩⟩
--   = (f 0 Vec.nil = nilD
--     ∧ ((n : Nat) -> (a : A) -> (v : Vec A n) -> (f (n + 1) (Vec.cons n a v) = consD n a /- v -/ (f n v)))
--     ∧ True)
--   := rfl


-- # Substitutions

/-- Represents a substitution from Δₛ to Γₛ.
Note that `Subₛ` is essentially a list of the same length as the context `Δₛ`.
This is because for every entry in the context Δₛ we will substitute it
with a Γₛ-term saved in `Subₛ`, thus the resulting context will be Γₛ.  -/
inductive Subₛ : (Γₛ : Conₛ) -> (Δₛ : Conₛ) -> Type (u+1)
| nil : Subₛ Γₛ .nil
| cons : Subₛ Γₛ Δₛ -> Tmₛ Γₛ Aₛ -> Subₛ Γₛ (Aₛ :: Δₛ)

/-- Substitutes a variable `v ∈ Δₛ` with a Γₛ-term. -/
def SubₛVar : Varₛ Δₛ Aₛ -> Subₛ Γₛ Δₛ -> Tmₛ Γₛ Aₛ
| .vz  , .cons _ t => t
| .vs v, .cons σ _ => SubₛVar v σ

/-- Applies the substitution to a term, resulting in a new term in the new context. -/
def SubₛTm : {Aₛ : _} -> Tmₛ Δₛ Aₛ -> Subₛ Γₛ Δₛ -> Tmₛ Γₛ Aₛ
| _, .var v, σ => SubₛVar v σ
-- | _, .app (A := _A) t u, σ => .app (SubₛTm t σ) u

def SubₛTy : Tyₚ Δₛ -> Subₛ Γₛ Δₛ -> Tyₚ Γₛ
| El Self, σ => El (SubₛTm Self σ)
| PArr T Rest, σ => PArr T (SubₛTy Rest σ)
| PFunc Self Rest, σ => PFunc (SubₛTm Self σ) (SubₛTy Rest σ)

def SubₛCon : Conₚ Δₛ -> Subₛ Γₛ Δₛ -> Conₚ Γₛ
| [], _ => []
| A :: Γ, σ => SubₛTy A σ :: SubₛCon Γ σ

/-- Increment all de brujin indices in this term by one. -/
def vshift : {Aₛ : Tyₛ} -> Tmₛ Γₛ Aₛ -> Tmₛ (Bₛ :: Γₛ) Aₛ
| _, .var v => .var (.vs v)
-- | _, .app (A := _A) t u => .app (vshift t) u

/-- Weakens a substitution.
  Given a substitution `σ` which replaces all variables `Δₛ ⊢ v` with terms `Γₛ ⊢ t`,
  the weakened substitution will replace all variables `Δₛ ⊢ v` with terms `Γₛ, Aₛ ⊢ t`.
  The stored terms thus need to be shifted using `vshift`. -/
def weaken.{u} : {Γₛ Δₛ : Conₛ.{u}} -> {Aₛ : Tyₛ.{u}} -> Subₛ.{u} Γₛ Δₛ -> Subₛ (Aₛ :: Γₛ) Δₛ
| Γₛ, .nil    , Aₛ, .nil => .nil
| Γₛ, Bₛ :: Δₛ, Aₛ, .cons σ t => Subₛ.cons (weaken σ) (vshift t)

/-- Identity substitution. Does nothing (replaces all variables by itself). -/
def Subₛ.id : (Γₛ : Conₛ) -> Subₛ Γₛ Γₛ
| .nil => .nil
| .cons _ Γₛ => .cons (weaken (Subₛ.id Γₛ)) (.var .vz)

theorem aux : @Eq (Tmₛ (Bₛ :: Γₛ) Aₛ) (vshift (SubₛVar v (Subₛ.id Γₛ))) (SubₛVar v (weaken (Subₛ.id Γₛ))) := by
  induction v generalizing Bₛ with
  | vz => simp [vshift, SubₛVar, weaken, Subₛ.id]
  | @vs Γₛ Aₛ' Cₛ v ih =>
    have h : @Eq (Tmₛ (Bₛ :: Cₛ :: Γₛ) Aₛ')
      (vshift <| SubₛVar v <| weaken <| Subₛ.id Γₛ)
      (vshift <| vshift <| SubₛVar v <| Subₛ.id Γₛ)
      := congrArg vshift ih.symm
    simp only [SubₛVar]
    simp only [Subₛ.id, weaken, vshift, SubₛVar]
    -- rw [h]
    -- simp [<- ih]
    -- rw [ih] at h
    sorry

theorem SubₛVar_id : (v : Varₛ Γₛ Aₛ) -> SubₛVar v (Subₛ.id Γₛ) = Tmₛ.var v := fun v => by
  induction v with
  | vz => rw [Subₛ.id]; rfl
  | @vs Γₛ Aₛ Bₛ v ih =>
    rw [Subₛ.id]
    rw [SubₛVar]
    have ih : @Eq (Tmₛ (Bₛ :: Γₛ) Aₛ)
      (vshift (SubₛVar v (Subₛ.id Γₛ)))
      (vshift (Tmₛ.var v))
      := congrArg vshift ih
    simp [vshift] at ih
    rw [<- aux]
    exact ih

theorem SubₛTm_id : (t : Tmₛ Γₛ Aₛ) -> SubₛTm t (Subₛ.id Γₛ) = t
| .var v => SubₛVar_id v
-- | .app (A := Aₛ) t u => sorry

def SubₛA : Subₛ Γₛ Δₛ -> ConₛA Γₛ -> ConₛA Δₛ
| .nil     ,  _ => ⟨⟩
| .cons σ t, γₛ => ⟨TmₛA t γₛ, SubₛA σ γₛ⟩

def SubₛD : (σ : Subₛ Γₛ Δₛ) -> ConₛD Γₛ γₛ -> ConₛD Δₛ (SubₛA σ γₛ)
| .nil, γₛD => ⟨⟩
| .cons σ t, γₛD => ⟨TmₛD t γₛD, SubₛD σ γₛD⟩

def SubₛS : (σ : Subₛ Γₛ Δₛ) -> ConₛS Γₛ γₛ γₛD -> ConₛS Δₛ (SubₛA σ γₛ) (SubₛD σ γₛD)
| .nil, γₛD => ⟨⟩
| .cons σ t, γₛD => ⟨TmₛS t γₛD, SubₛS σ γₛD⟩


-- ## Now for Points...

inductive Varₚ : Conₚ Γₛ -> Tyₚ Γₛ -> Type (u+1)
| vz :               Varₚ (Aₛ :: Γₛ) Aₛ
| vs : Varₚ Γₛ Aₛ -> Varₚ (Bₛ :: Γₛ) Aₛ

set_option genInjectivity false in
inductive Tmₚ.{u} {Γₛ : Conₛ.{u}} : Conₚ.{u} Γₛ -> Tyₚ.{u} Γₛ -> Type (u+1)
| var : Varₚ Γ A -> Tmₚ Γ A
| app {T : Type u} {A : Tyₚ Γₛ} : Tmₚ Γ (PArr T A)   -> (t : T)      -> Tmₚ Γ A
| appr             {A :      Tyₚ Γₛ} : Tmₚ Γ (PFunc a A) -> Tmₚ Γ (El a) -> Tmₚ Γ A

/-- Represents a substitution from Δₛ to Γₛ.
Note that `Subₛ` is essentially a list of the same length as the context `Δₛ`.
This is because for every entry in the context Δₛ we will substitute it
with a Γₛ-term saved in `Subₛ`, thus the resulting context will be Γₛ.  -/
inductive Subₚ : (Γ : Conₚ Γₛ) -> (Δ : Conₚ Δₛ) -> Type (u+1)
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

def vsₚ : {A : Tyₚ Γₛ} -> Tmₚ Γ A -> Tmₚ (B :: Γ) A
| _, .var v => .var (.vs v)
| _, .app (A := _A) t u => .app (vsₚ t) u
| _, .appr (A := _A) t u => .appr (vsₚ t) (vsₚ u)

def weakenₚ.{u} : {Γ Δ : Conₚ.{u} Γₛ} -> {A : Tyₚ.{u} Γₛ} -> Subₚ.{u} Γ Δ -> Subₚ (A :: Γ) Δ
| _, .nil  , _, .nil => .nil
| _, _ :: _, _, .cons σ t => Subₚ.cons (weakenₚ σ) (vsₚ t)

def Subₚ.id : (Γ : Conₚ Γₛ) -> Subₚ Γ Γ
| .nil => .nil
| .cons _ Γ => .cons (weakenₚ (Subₚ.id Γ)) (.var .vz)

theorem SubₚTm_id (t : Tmₚ Γ A) : SubₚTm t (Subₚ.id Γ) = t := sorry


def VarₚA : Varₚ Γ A -> ConₚA Γ γₛ -> TyₚA A γₛ
| .vz  , ⟨a, _⟩ => a
| .vs v, ⟨_, γ⟩ => VarₚA v γ

def TmₚA.{u} : {A : Tyₚ Γₛ} -> Tmₚ.{u} Γ A -> ConₚA.{u} Γ γₛ -> TyₚA.{u} A γₛ
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
theorem TmₚA_var : TmₚA (Tmₚ.var v) γₛ = VarₚA v γₛ := by rfl

def TmₚD : (t : Tmₚ Γ A) -> ConₚD Γ γₛD γ -> TyₚD A γₛD (TmₚA t γ)
| .var v, γD => VarₚD v γD
| .app (A := _A) t u, γD => TmₚD t γD u
| .appr (A := A) t u, γD => TmₚD t γD (TmₚD u γD)

def SubₚD : (σ : Subₚ Γ Δ) -> ConₚD Γ γₛD γ -> ConₚD Δ γₛD (SubₚA σ γ)
| .nil, γD => ⟨⟩
| .cons σ t, γD => ⟨TmₚD t γD, SubₚD σ γD⟩


-- # Sort and Points Constructors

-- The paper assumes `u := 0` but we generalize a little.
universe u
variable {Ωₛ : Conₛ.{u}}
variable {Ω : Conₚ.{u} Ωₛ}

/-- This is a lambda telescope which eventually produces a type for the point terms term Ω⊢t.
  Then later constrTmₚ will produce the actual terms which inhabit this type.
  We will soon prove *coherence* of this, which will "pull back" any meaning about the syntactic terms and types
  to meaning about the actual Lean terms and types.

Example.
Try not to get confused by `V String`, just imagine it's one identifier.
```
constrTmₛ' (Ω := V String) (Ωₛ := Vₛ) (Aₛ := (SPi Nat (fun _ => U))) (.var .vz)
```
reduces to
```
fun (n : Nat) => Tmₚ (V String) (El ((.var .vz) @ n))    :   Nat -> Type
```
which is a stand-in for `Vec String : Nat -> Type`.
We do not have an actual `Vec String`, so instead we use `constrTmₛ (V String)`
-/
def constrTmₛ' : {Aₛ : Tyₛ.{u}} -> Tmₛ.{u} Ωₛ Aₛ -> TyₛA.{u, u + 1} Aₛ -- baked-in ULift into TyₛA
| U      , t => Tmₚ Ω (El t)
-- | SArr _ _, t => fun u => constrTmₛ' (.app t u)

#reduce TyₛA U
-- example : TyₛA.{0, 1} U := constrTmₛ' (Ω := V String) (Ωₛ := Vₛ) ((.var .vz) @ 123)
-- #reduce TyₛA (SPi Nat (fun _ => U))
-- example : TyₛA (SPi Nat (fun _ => U)) := constrTmₛ' (Ω := V String) (Ωₛ := Vₛ) (.var .vz)

-- example : constrTmₛ' (Ω := V String) (Ωₛ := Vₛ) (Aₛ := (SPi Nat (fun _ => U))) (.var .vz)
--   = fun (n : Nat) => Tmₚ (V String) (El ((.var .vz) @ n))
--   := rfl

def constrₛ' : Subₛ Ωₛ Γₛ -> ConₛA Γₛ
| .nil => ⟨⟩
| .cons σ t => ⟨constrTmₛ' (Ω := Ω) t, constrₛ' σ⟩

def constrₛ : ConₛA Ωₛ := constrₛ' (Ω := Ω) (Subₛ.id Ωₛ)

-- example : constrₛ (Ωₛ := Vₛ) (Ω := V String)
--   = ⟨fun u => Tmₚ (V String) (El ((Tmₛ.var .vz) @ u)), ⟨⟩⟩
--   := rfl

-- Lemma 16
theorem constrₛ_coherent (t : Tmₛ Γₛ Aₛ) (σ : Subₛ Ωₛ Γₛ) : TmₛA t (@constrₛ' Ωₛ Ω Γₛ σ) = @constrTmₛ' Ωₛ Ω _ (SubₛTm t σ) := by
  induction σ with
  | nil => sorry
  | cons σ u ih_σ =>
    induction t with
    | var v =>
      cases v with
      | vz =>
        rw [TmₛA]
        rw [constrₛ']
        -- rw [VarₛA]
        rfl
      | vs v =>
        rw [TmₛA]
        rw [constrₛ']
        -- rw [VarₛA]
        -- rw [constrTmₛ']
        -- rw [ih_σ]
        sorry
        done


-- same as the above
example (t : Tmₛ Γₛ Aₛ) : (TmₛA t) ∘ (@constrₛ' Ωₛ Ω Γₛ) = (@constrTmₛ' Ωₛ Ω _) ∘ (SubₛTm t)
  := funext <| constrₛ_coherent t

-- example
--   : @TyₚA Vₛ (PPi Nat fun n => @El Vₛ ((.var vz) @ n)) (@constrₛ Vₛ (V String))
--   -- = ((n : Nat) -> (fun n => Tmₚ (V String) (El ((.var .vz) @ n))) n) -- intermediate step
--   = ((n : Nat) -> Tmₚ (V String) (El ((.var .vz) @ n)))
--   := rfl
-- example --       vvvvvvvvvvvvvvvvvv "Self"
--   : @TyₚA Vₛ (El ((.var vz) @ 123)) (@constrₛ Vₛ (V String))
--   = Tmₚ (V String) (El ((.var .vz) @ 123))
--   := rfl

def constrTmₚ' : {A : Tyₚ _} -> Tmₚ Ω A -> TyₚA A (constrₛ (Ω := Ω))
| El Self, t => by
  -- this is actually `⊢ Tmₚ Ω (El Self)` but lean isn't smart enough
  rw [TyₚA]
  rw [constrₛ]
  rw [constrₛ_coherent Self]
  rw [SubₛTm_id]
  exact t
| PArr T A, t => fun τ => constrTmₚ' (.app t τ)
| PFunc Self A, t =>
  fun u =>
    let u : Tmₚ Ω (El Self) := by
      rw [constrₛ] at u
      rw [constrₛ_coherent Self] at u
      rw [SubₛTm_id] at u
      exact u
    constrTmₚ' (.appr t u)

def constrₚ' : Subₚ Ω Γ -> ConₚA Γ (constrₛ (Ω := Ω))
| .nil => ⟨⟩
| .cons σ t => ⟨constrTmₚ' (Ω := Ω) t, constrₚ' σ⟩

def constrₚ := constrₚ' (Subₚ.id Ω)

theorem constrₚ_coherent (ttt : Tmₚ Γ A) (σ : Subₚ Ω Γ) : TmₚA ttt (@constrₚ' Ωₛ Ω Γ σ) = @constrTmₚ' Ωₛ Ω _ (SubₚTm ttt σ) := by
  sorry


-- # Eliminator

variable (ωₛD : ConₛD Ωₛ constrₛ) (ωₛ : ConₚD Ω ωₛD constrₚ)

def elimTmₛ' : {Aₛ : Tyₛ.{u}} -> (t : Tmₛ.{u} Ωₛ Aₛ) -> TyₛS.{u, u+1} Aₛ (TmₛA t (constrₛ (Ω:=Ω))) (TmₛD t ωₛD)
| U, a =>
  -- a : Tmₛ Ωₛ U
  -- ⊢ TyₛS U (TmₛA a constrₛ) (TmₛD a ωₛD)
  -- have (t : TmₛA a (constrₛ (Ω:=Ω))) : TyₛS U (TmₛD a ωₛD t) = TmₛD a ωₛD t := sorry

  fun (t : TmₛA a constrₛ) => by
    -- ⊢ TmₛD a ωₛD t
    -- let ret := TmₛD t ωₛD
    sorry
-- | SPi T Aₛ, t =>
--   fun τ => by
--     let res := elimTmₛ' (.app t τ)
--     -- why is this so ass
--     rw [TyₛS_helper TmₛA_app] at res
--     rw [TmₛD_app] at res
--     simp only [eq_symm_cancel, eq_cast_trans] at res
--     exact res

def elimₛ' : (σ : Subₛ Ωₛ Γₛ) -> ConₛS Γₛ (SubₛA σ constrₛ) (SubₛD σ ωₛD)
| .nil => ⟨⟩
| .cons σ t => ⟨elimTmₛ' (Ω := Ω) ωₛD t, elimₛ' σ⟩






namespace Example
  def List (A : Type) : Type 1                         := constrTmₛ' (Ω := V A) (.var .vz)
  def List.nil (A : Type) : List A                     := constrTmₚ' (Ω := V A) (.var .vz)
  def List.cons (A : Type) : (x:A) -> List A -> List A := constrTmₚ' (Ω := V A) (.var (.vs .vz))

end Example
