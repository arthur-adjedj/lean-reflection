import Lean
import Reflection.MutualInductive
import Qq

open Lean Meta Elab Term Qq
open Reflection MutualInductive

namespace Reflection.MutualInductive.Derive

private partial def getTyₛ (tys : Expr) : MetaM Q(Tyₛ.{u}) := do
  forallBoundedTelescope tys (some 1) fun var body => do
    if var.isEmpty then
      return q(Tyₛ.U.{u})
    else
      let var := var[0]!
      let ty : Q(Type u) <- var.fvarId!.getType
      let rest : Q(Tyₛ.{u}) <- getTyₛ body -- rest is for example `var : X ⊢ SPi ...`
      let rest : Q($ty -> Tyₛ.{u}) <- mkLambdaFVars #[var] rest
      return q(Tyₛ.SPi.{u} $ty $rest)

partial def skipParams (tys : Expr) (nParams : Nat) (cont : Expr -> MetaM Expr) : MetaM Expr :=
  match nParams with
  | 0 => cont tys
  | nParams + 1 => do
    forallBoundedTelescope tys (some 1) fun var body => do
      let body' <- skipParams body nParams cont
      if body'.containsFVar var[0]!.fvarId! then mkLambdaFVars var body'
      else return body'

elab "Tyₛ% " tys:term : term => do
  let tys <- elabTerm tys none
  let u <- mkFreshLevelMVar
  getTyₛ (u:=u) tys

elab "Tyₛ! " T:term : term => do
  let T <- elabTerm T none
  let ⟨I, args⟩ := T.getAppFnArgs
  let info <- getConstInfoInduct I
  if info.numParams != args.size then throwError m!"Expected {info.numParams} params."
  let u <- mkFreshLevelMVar
  skipParams info.type info.numParams (getTyₛ (u := u))

elab "Conₛ! " T:term : term => do
  let T <- elabTerm T none
  let ⟨I, args⟩ := T.getAppFnArgs
  let info <- getConstInfoInduct I
  if info.numParams != args.size then throwError m!"Expected {info.numParams} params."
  let u <- mkFreshLevelMVar
  info.all.foldlM (fun (acc : Q(Conₛ.{u})) name => do
    let info <- getConstInfoInduct name
    let u <- mkFreshLevelMVar
    let ty : Q(Tyₛ.{u}) <- skipParams info.type info.numParams (getTyₛ (u := u))
    return q(Conₛ.ext $acc $ty)
  ) q(Conₛ.nil.{u})

#check Tyₛ% (Nat -> Type)
#check Tyₛ! (Vec String)
#check Conₛ! (Vec String)

-- /-- Given a `T` such as `Vec 123 : Type`, produce `Tmₛ.app (Tmₛ.var Varₛ.vz) 123 : Tmₛ _ Tyₛ.U`.
--   Given `Vec : Nat -> Type`, produce `Tmₛ.var Varₛ.vz : Tmₛ _ (Tyₛ.SPi Nat fun _ => Tyₛ.U)`. -/
-- private partial def getTmₛ (Γₛ : Q(Conₛ.{u})) (Aₛ : Q(Tyₛ.{u})) (T : Expr) : MetaM Q(Tmₛ.{u} $Γₛ $Aₛ) := do
--   match <- Meta.whnf T with
--   | .app t u =>
--     let t := t
--     let tt <- getTmₛ Γₛ Aₛ t
--     sorry
--     -- q(Tmₛ.app )
--   | .fvar _ => q(Tmₛ.var Varₛ.vz)
--   | _ => throwError "uh oh"

-- elab "%Tmₛ " T:term : term => do
--   let T <- elabTerm T none
--   -- let  := T.getAppFn
--   let ind <- getConstInfoInduct (getAppFn)
--   getTyₚ ind.type

partial def getTyₚ (Γₛ : Q(Conₛ.{u})) (tys : Expr) : MetaM Q(Tyₚ.{u} $Γₛ) := do
  forallBoundedTelescope tys (some 1) fun var body => do
    if var.isEmpty then
      return q(Tyₛ.U.{u})
    else
      let var := var[0]!
      let ty : Q(Type u) <- var.fvarId!.getType
      let rest : Q(Tyₛ.{u}) <- getTyₛ body -- rest is for example `var : X ⊢ SPi ...`
      let rest : Q($ty -> Tyₛ.{u}) <- mkLambdaFVars #[var] rest
      return q(Tyₛ.SPi.{u} $ty $rest)
  -- forallBoundedTelescope args (some 1) fun var body => do
  --   let u <- mkFreshLevelMVar
  --   if var.isEmpty then
  --     -- body is e.g. `Vec 123`.
  --     let T <- getTmₛ Γₛ q(Tyₛ.U) body
  --     return q(Tyₚ.El $(T))
  --   else
  --     let var := var[0]!
  --     let ty : Q(Type u) <- var.fvarId!.getType
  --     let rest : Expr <- getTyₛ body -- rest is for example `var : X ⊢ SPi ...`
  --     let rest : Q($ty -> Tyₛ.{u}) <- mkLambdaFVars #[var] rest -- rest is for example `⊢ fun var:X => SPi ...`
  --     return q(Tyₛ.SPi.{u} $ty $rest)

elab "%Tyₚ " i:ident : term => do
  let ind <- getConstInfoInduct i.getId
  getTyₚ ind.type

#check Vec
#check %Tyₛ Vec
