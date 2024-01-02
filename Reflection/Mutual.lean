-- Adaptation of https://dx.doi.org/10.4230/LIPIcs.FSCD.2020.23 for Lean4.
-- Agda source for the above lives at https://bitbucket.org/javra/inductive-families

-- # Syntax

inductive Tyₛ : Type 1
| U : Tyₛ
| SPi : (T : Type) -> (T -> Tyₛ) -> Tyₛ
open Tyₛ

inductive Conₛ
| nil : Conₛ
| cons : Tyₛ -> Conₛ -> Conₛ
notation "[]" => Conₛ.nil
infixr:67 " :: " => Conₛ.cons

inductive Varₛ : Conₛ -> Tyₛ -> Type 1
| vz :               Varₛ (Aₛ :: Γₛ) Aₛ
| vs : Varₛ Γₛ Aₛ -> Varₛ (_  :: Γₛ) Aₛ
open Varₛ

set_option genInjectivity false in
/-- `t : Tmₛ Γ A` corresponds to `Γ ⊢ t : A`. -/
inductive Tmₛ : Conₛ -> Tyₛ -> Type 1
/-- A variable is a term.
```-
(a : A) ∈ Γ
-----------var
Γ ⊢ₛ a : A
``` -/
| var : Varₛ Γ A -> Tmₛ Γ A
/-- Function application. Maybe problematic because `arg` is a black box.
```-
Γ ⊢ₛ f : (x : T) -> A x      arg : T
-------------------------------------app-Intro
Γ ⊢ₛ f arg : A arg
``` -/
| app : Tmₛ Γ (SPi T A) -> (arg : T) -> Tmₛ Γ (A arg)
infixl:50 " @ " => Tmₛ.app

/-- Constructor types `... -> Self ...`.

The only way to create a `Tyₚ` is by ending it with a `El`, which must be a term in the universe `U`.
The only way to create a term like that is by using `Tmₛ.app` and `Tmₛ.var`.
For example the variables are `Even` and `Odd`, i.e. the other types in the mutual block being defined,
then `Even @ 123` is a term in universe `U`. -/
inductive Tyₚ : Conₛ -> Type 1
| El : Tmₛ Γₛ U -> Tyₚ Γₛ
| PPi   : (T : Type) -> (T -> Tyₚ Γₛ) -> Tyₚ Γₛ
/-- Allows us to introduce nested binders `(x : Self ...) -> ...`.
  `PFunc` is non-dependent, because it makes no sense to have `(self : Self ...) -> Self self`.
  (...but once you have ind-ind or ind-rec, it might be possible?) -/
| PFunc : Tmₛ Γₛ U   ->       Tyₚ Γₛ  -> Tyₚ Γₛ
open Tyₚ

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
  def V_cons (A : Type) : Tyₚ Vₛ :=
    PPi Nat fun n => -- (n : Nat) ->
      PPi A fun _ => -- A ->
        PFunc ((Tmₛ.var vz) @ n) <| -- Vec n ->
          El ((Tmₛ.var vz) @ (n + 1)) -- Vec (n + 1)

  def V (A : Type) : Conₚ Vₛ := V_nil :: V_cons A :: []
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
by giving it the actual `Vec` interpretation via the `γₛ : ConₛA Γₛ`. -/
def TmₛA : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> Tmₛ Γₛ Aₛ -> ConₛA Γₛ -> TyₛA Aₛ
| Γ, A, @Tmₛ.var _   _ v  , γₛ => VarₛA v γₛ
| Γ, _, @Tmₛ.app Γ T A t u, γₛ => (TmₛA t γₛ) u

example {Vec : Nat -> Type} : @TmₛA (SPi Nat (fun _ => U) :: []) U ((.var .vz) @ 123) ⟨Vec, ⟨⟩⟩ = Vec 123 := rfl

/-- Interprets a constructor type. See below for examples. -/
def TyₚA : Tyₚ Γₛ -> ConₛA Γₛ -> Type
| El    Self, γₛ => TmₛA Self γₛ
| PPi   T    Rest, γₛ => (arg : T)    -> TyₚA (Rest arg) γₛ
| PFunc Self Rest, γₛ => TmₛA Self γₛ -> TyₚA Rest γₛ

example {Vec : Nat -> Type} {_A : Type} : @TyₚA (SPi Nat (fun _ => U) :: []) V_nil ⟨Vec, ⟨⟩⟩ = (Vec 0)
  := rfl

example {Vec : Nat -> Type} {A : Type}
  : @TyₚA (SPi Nat (fun _ => U) :: []) (V_cons A) ⟨Vec, ⟨⟩⟩
  = ((n : Nat) -> A -> Vec n -> Vec (n + 1))
  := rfl

def ConₚA : Conₚ Γₛ -> ConₛA Γₛ -> Type
| .nil, _ => PUnit
| .cons A Γ, γₛ => TyₚA A γₛ × ConₚA Γ γₛ
