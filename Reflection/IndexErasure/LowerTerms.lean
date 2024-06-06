import Reflection.MInd
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
-- open Qq

def lowerDef (e : Expr) : MetaM Expr := do
  sorry

def lowerInduct (e : Expr) : MetaM Expr := do
  let Γₛ : Expr := sorry
  let Γₚ : Expr := sorry

  sorry
  -- let ΓₚE : Q(Conₚ $ΓₛE) := mkApp2 q(@eConₚ.{0}) Γₛ Γₚ
  -- let γₛE : Q(EConₛA.{0,0} $Γₛ)      := mkApp2 q(@mkConₛ.{0}) ΓₛE ΓₚE
  -- let γₚE : Q(EConₚA.{0,0} $Γₚ $γₛE) := mkApp2 q(@mkConₚ.{0}) ΓₛE ΓₚE

  -- let ΓₛG : Q(Conₛ.{0}) := mkApp2 q(@gConₛ.{0}) Γₛ γₛE
  -- let ΓₚG : Q(Conₚ $ΓₛG) := mkApp4 q(@gConₚ) Γₛ γₛE Γₚ γₚE
  -- let γₛG /- : Q(GConₛA.{0,0} ..) -/ := mkApp2 q(@mkConₛ.{0}) ΓₛG ΓₚG
  -- let γₚG /- : Q(GConₚA.{0,0} ..)-/ := mkApp2 q(@mkConₚ.{0}) ΓₛG ΓₚG
  -- -- let L : Q(Type) := q(@Sigma )
-- #exit

/-- Given `Vec 123`, produces `VecL 123`. -/
def lowerTmₛ (e : Expr) : MetaM Expr := do
  sorry

/-- Given `Vec.cons`, produces `VecL.cons`. -/
def lowerTyₚ (e : Expr) : MetaM Expr := do
  sorry

/-- Lowers a term.  -/
def lowerTm (e : Expr) : MetaM Expr := do
  match e with
  | .app f a =>
    -- `⊢ f : Pi A B`
    -- `⊢ a : A`
    -- `f a : B[a]`
    -- `⊢ fᴸ : Pi Aᴸ Bᴸ`
    return .app (<- lowerTm f) (<- lowerTm a)
  -- | .lam .. => sorry
  | .const name _ =>
    match <- getConstInfo name with
    | .inductInfo _ => lowerInduct e
    | .ctorInfo _ => lowerTyₚ e
    | .defnInfo _ => lowerDef e
    | _ => throwError "lowerEnv: unsupported const kind for {name}"
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
partial def lowerTy (u : Level) (e : Expr) : MetaM Expr := do
  if let Expr.sort _ := e then -- case `U : Ty Γ`
    return e
  else if let .forallE _ A _ _ := e then -- case `Pi A B : Ty Γ`
    Meta.forallBoundedTelescope e (some 1) fun a_fv B => do
      let Γ_A <- getLCtx -- `Γ, A` and `Γ, A ⊢ B`
      let AL : Expr <- lowerTy u A -- Γᴸ ⊢ Aᴸ
      let BL : Expr <- lowerTy u B -- (Γ, A)ᴸ ⊢ Bᴸ    is (hopefully) well-typed again.
      let Γ_AL := Γ_A.modifyLocalDecl a_fv[0]!.fvarId! (fun ldecl => ldecl.setType AL)
      withLCtx Γ_AL (<- getLocalInstances) do
        mkForallFVars a_fv BL
  else if let .fvar fv := e then
    -- `⊢ a : A` gets casted to `⊢ aL : Aᴸ`. Since metaprogramming is untyped, this is a no-op.
    return .fvar fv
  else -- case `El T : Ty Γ`
    lowerTm e
    -- let T := e.getAppFn
    -- let args := e.getAppArgs
    -- let v <- mkFreshLevelMVar
    -- if <- isDefEq T (.const ``Vec [v]) then
    --   let n := args[1]!
    --   return mkAppN (.const ``Sigma [u, u]) #[.const ``Example.VecE [u], .app (.const ``Example.VecG [u]) n]
    -- else if T.isAppOf ``Eq then return mkAppN (.const ``Eq [.zero]) args
    -- else if T.isAppOf ``Nat || T.isAppOf ``String then return e
    -- else throwError "oh no, {e}"

-- open Example
@[irreducible] def len  : Vec String n -> Nat := fun _ => n

elab "lower! " T:term : term => do
  let T <- elabTerm T none
  let u <- Meta.mkFreshLevelMVar
  lowerTy (u := u) T

#check ∀n, ∀x, lower! ∀v, len (Vec.cons n x v) = (len v) + 1
/- (n : Nat) → (x : String) → (v : PSigma (VecG n)) → TEq (len (Vec.cons n x v)) (len v + 1) -/

-- #eval lowerTy q((v : MutualInductive.Vec String (nat_lit 0)) -> TEq (len (Vec.cons 0 "a" v)) ((len v) + 1))
