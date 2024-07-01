import Reflection.MInd
import Reflection.MInd.Derive
import Reflection.IndexErasure.Erase
import Reflection.IndexErasure.Guard
import Reflection.IndexErasure.Lower

namespace Reflection.IndexErasure

set_option pp.fieldNotation.generalized false
open Reflection MInd
open Tyₛ Tyₚ Varₛ Varₚ

/-
  ## Lowering Terms
  This is done via good old Lean metaprogramming.
-/

open Lean Elab Term Meta
open Derive Qq

/-- Lowers a definition declaration. Expects `e` to be of form `Expr.const ..`,
  *without args*, since monomorphization isn't handled here by index erasure. -/
def lowerDef (e : Expr) : MetaM Expr := do
  sorry

#check @Derive.getConₛ

/-- Lowers an inductive type to the product of the type-index erased version and its guard.
  For example maps `Vec` to `fun (n : Nat) => (e : VecE) × VecG n e`.
  Works with mutual inductive blocks.  -/
def lowerTmₛ {Aₛ : Q(Tyₛ.{u})} (T : Q(TyₛA.{u, u} $Aₛ)) : MetaM Q(TyₛA.{u, u+2} $Aₛ) := do
  let .const n _lvls := T.getAppFn | throwError "lowerTmₛ: T isn't an app of a const"
  let ii <- getConstInfoInduct n
  let u <- mkFreshLevelMVar
  let Ωₛ : Q(Conₛ.{u}) <- getConₛ (u := u) ii
  let Ωₚ : Q(Conₚ.{u} $Ωₛ) <- getConₚ (u := u) ii Ωₛ
  let T : Q(Tmₛ $Ωₛ $Aₛ) <- getTmₛ ii.all Ωₛ Aₛ T
  let L := q(mkLTyₛ.{u} $Ωₛ $Ωₚ $T)
  return L

elab "asdf" : term => lowerTmₛ (u := 0) (Aₛ := q(.U)) q(Derive.Vec 132)
def chk : Type 2 := asdf
#print chk
#reduce chk

/-- Given the type of `Vec.cons`, produces the type of `VecL.cons`. -/
def lowerTyₚ (e : Expr) : MetaM Expr := do
  sorry

/-- Lowers a term.  -/
def lowerTmₚ (e : Expr) : MetaM Expr := do
  match e with
  | .app f a =>
    -- `⊢ f : Pi A B`
    -- `⊢ a : A`
    -- `f a : B[a]`
    -- `⊢ fᴸ : Pi Aᴸ Bᴸ`
    return .app (<- lowerTmₚ f) (<- lowerTmₚ a)
  -- | .lam .. => sorry
  -- | .const name _ =>
  --   match <- getConstInfo name with
  --   | .inductInfo _ => lowerTmₛ e
  --   | .ctorInfo _ => lowerTyₚ e
  --   | .defnInfo _ => lowerDef e
  --   | _ => throwError "lowerEnv: unsupported const kind for {name}"
  | _ => throwError "oh no, lowerTm {e}"

/-- Lowers a type. `lower : Ty Γ -> Ty Γᴸ`
```
def lowerTy : {Γ : Con} -> Ty Γ -> Ty Γᴸ
| Γ, .Pi A B => -- where `Ty.Pi : (A : Ty Γ) -> Ty (Γ, A) -> Ty Γ`
  let AL : Ty Γᴸ := lowerTy A
  let BL : Ty (Γᴸ, Aᴸ) := lowerTy B -- because `(Γ, A)ᴸ ≣ (Γᴸ, Aᴸ)`
  .Pi AL BL -- typechecks
| Γ, El T => sorry
``` -/
partial def lowerTy (u : Level) (e : Q(Type u)) : MetaM Q(Type u) := do
  if let Expr.sort _ := e then -- case `U : Ty Γ`
    return e
  else if let .forallE _ A _ _ := e then -- case `Pi A B : Ty Γ`
    let uA <- mkFreshLevelMVar
    let A : Q(Type $uA) := A
    Meta.forallBoundedTelescope e (some 1) fun a_fv B => do
      let Γ_A <- getLCtx -- `Γ, A` and `Γ, A ⊢ B`
      let AL : Q(Type $uA) <- lowerTy uA A -- Γᴸ ⊢ Aᴸ
      let BL : Expr <- lowerTy u B -- (Γ, A)ᴸ ⊢ Bᴸ    is (hopefully) well-typed again.
      let Γ_AL := Γ_A.modifyLocalDecl a_fv[0]!.fvarId! (fun ldecl => ldecl.setType AL)
      withLCtx Γ_AL (<- getLocalInstances) do
        mkForallFVars a_fv BL
  else if let .fvar fv := e then
    -- `⊢ a : A` gets casted to `⊢ aL : Aᴸ`. Since metaprogramming is untyped, this is a no-op.
    return .fvar fv
  else -- case `El T : Ty Γ`
    let Aₛ <- mkFreshExprMVarQ q(Tyₛ.{u})
    lowerTmₛ (u := u) (Aₛ := Aₛ) e

@[irreducible] def len : Vec String n -> Nat := fun _ => n

elab "lower! " T:term : term => do
  let T <- elabTerm T none
  let u <- Meta.mkFreshLevelMVar
  lowerTy (u := u) T

def test₁ := lower! Derive.Vec 123
#print test₁

def test₂ := lower! Derive.Vec
#print test₂

#check ∀n, ∀x, lower! ∀v, len (Vec.cons n x v) = (len v) + 1

  -- indexErase
  -- mono
  -- cvc5
