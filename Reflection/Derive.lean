import Lean
import Reflection.MutualInductive
import Qq

open Lean Meta Elab Term Qq
open Reflection MutualInductive

namespace Reflection.MutualInductive.Derive

/-- Reads in `Nat -> Type`. -/
partial def getTyₛ (τ : Q(Type (u+1))) : MetaM Q(Tyₛ.{u}) := do
  forallBoundedTelescope τ (some 1) fun var body => do
    if var.isEmpty then
      return q(Tyₛ.U.{u})
    else
      let var := var[0]!
      let ty : Q(Type u) <- var.fvarId!.getType
      let rest : Q(Tyₛ.{u}) <- getTyₛ body -- rest is for example `var : X ⊢ SPi ...`
      let rest : Q($ty -> Tyₛ.{u}) <- mkLambdaFVars #[var] rest
      return q(Tyₛ.SPi.{u} $ty $rest)

set_option pp.universes true in
#print Nₛ
#eval getTyₛ (u := .zero) q(Type)
#eval getTyₛ (u := .zero) q(Nat -> Type)

def _root_.List.indexOf [BEq α] : List α -> α -> Option Nat
| []     , _ => none
| x :: xs, a => if x == a then some 0 else (indexOf xs a).map (. + 1)

partial def Conₛ.recMeta {motive : Q(Type u)} (Γₛ : Q(Conₛ.{u}))
  (case_nil : MetaM Q($motive))
  (case_ext : Q(Conₛ.{u}) -> MetaM Q($motive) -> Q(Tyₛ.{u}) -> MetaM Q($motive))
  : MetaM Q($motive)
  := do
    let Γₛ : Q(Conₛ.{u}) <- whnf Γₛ
    match Γₛ with
    | ~q(Conₛ.nil.{u}) => case_nil
    | ~q(Conₛ.ext.{u} $Δₛ $Bₛ) => case_ext Δₛ (Conₛ.recMeta Δₛ case_nil case_ext) Bₛ
    | _ => throwError "Conₛ.recMeta: nonexhaustive match, have Γₛ ≣ q({Γₛ})"

-- #check Tyₛ.SPi
-- #check Tyₛ.rec
-- /-
-- {motive : Tyₛ → Sort u_1} →
--   motive Tyₛ.U →
--   ((T : Type u) → (a : T → Tyₛ) →    ((a_1 : T) → motive (a a_1))    → motive (Tyₛ.SPi T a))
--   → (t : Tyₛ) → motive t
-- -/
-- partial def Tyₛ.recMeta {motive : Q(Type u)} (Aₛ : Q(Tyₛ.{u}))
--   (case_U : MetaM Q($motive))
--   (case_SPi : (T : Q(Type u)) -> Q($T -> Tyₛ.{u}) -> Q($T -> $motive) -> MetaM Q($motive))
--   : MetaM Q($motive)
--   := do
--     match Aₛ with
--     | ~q(Tyₛ.U.{u}) => case_U
--     | ~q(Tyₛ.SPi.{u} $T $f) => case_SPi T f (<- Tyₛ.recMeta )

def getVarₛ (n : Nat) (Γₛ : Q(Conₛ.{u})) (Aₛ : Q(Tyₛ.{u})) : MetaM Q(Varₛ.{u} $Γₛ $Aₛ) := do
  Conₛ.recMeta Γₛ
    (throwError "getVarₛ: Γₛ is nil")
    (fun Δₛ _ih Bₛ => do
      match n with
      | 0 =>
        let .true <- isDefEq Bₛ Aₛ | throwError "getVarₛ n=0: isDefEq failed: {Aₛ} is not defeq to {Bₛ}"
        return mkApp2 q(@Varₛ.vz.{u}) Δₛ Bₛ
      | n + 1 =>
        let var : Q(Varₛ $Δₛ $Aₛ) <- getVarₛ n Δₛ Aₛ
        return .app q(@Varₛ.vs $Δₛ $Aₛ $Bₛ) var
    )

def ctx : Q(Conₛ.{0}) := q((⬝ ▹ Tyₛ.U) ▹ Tyₛ.U)
#eval getVarₛ (u := 0) 0 ctx q(Tyₛ.U)
#eval getVarₛ (u := 0) 1 ctx q(Tyₛ.U)

#check @Tmₛ.app

/-- Reads in `Vec 123`. Make sure that `mblock` has the names of `Γₛ` in the same order. -/
partial def getTmₛ (mblock : List Name) (Γₛ : Q(Conₛ.{u})) (Aₛ : Q(Tyₛ.{u})) (T : Q(TyₛA.{u, u} $Aₛ)) : MetaM Q(Tmₛ.{u} $Γₛ $Aₛ) := do
  match T with
  | .const name _ =>
    let some idx := mblock.indexOf name | throwError "getTmₛ case Tyₛ.U: {T} does not belong to mutual block {mblock}"
    let var <- getVarₛ idx Γₛ Aₛ
    return q(Tmₛ.var $var)
  | .app f x => -- case `Vec 123 : TyₛA Aₛ`
    let ⟨u', ⟨X, x⟩⟩ <- inferTypeQ x -- x : X
    unless <- isLevelDefEq (.succ u) u' do throwError "getTmₛ level defeq failed, u ≣ {u}, but u' ≣ {u'}, with X ≣ {X}"
    -- let fTy <- inferType f
    let Bₛ : Q($X -> Tyₛ.{u}) <- mkFreshExprMVarQ q($X -> Tyₛ.{u})
    let fTy <- inferType f -- q(Nat -> Type)
    let fTy_code : Q(Tyₛ.{u}) <- getTyₛ (u := u) fTy -- q("Nat -> Type")
    let fTy_code_A : Q(Type (u+1)) := q(TyₛA.{u,u} $fTy_code) -- q("Nat -> Type"ᴬ) ≣ q((x : $X) -> "$Bₛ x"ᴬ)
    -- let fTy_expected := q((x : $X) -> TyₛA.{u,u} ($Bₛ x))
    unless <- isDefEq fTy_code_A q((x : $X) -> TyₛA.{u,u} ($Bₛ x)) do
      throwError "getTmₛ defeq type of f to function type failed, f : {<- inferType f}, X ≣ {X}, x ≣ {x}, Bₛ ≣ {Bₛ}\nfTy ≣ {()}\nfTy_code ≣ asdf"
    throwError "stop\nfTy ≣ {fTy}\nfTy_code ≣ {fTy_code}\nfTy_code_A ≣ {fTy_code_A}\nfTy_code_A₂ ≣ {q((x : $X) -> TyₛA.{u,u} ($Bₛ x))}"


    let f : Q((x : $X) -> TyₛA.{u,u} ($Bₛ x)) := f -- can do this because of the defeq check
    let f : Q(TyₛA.{u,u} ($Bₛ $x)) := f -- can do this because of the defeq check

    let sub <- getTmₛ mblock Γₛ fTy_code q($f)
    return mkAppN q(Tmₛ.app.{u}) #[] --#[Γₛ, X, Bₛ, f, x]
  | _ => throwError "oh no, getTmₛ {T}"

#check Vₛ
inductive Vec : Nat -> Type
#eval getTmₛ (u := .zero) [``Nat] q(Nₛ) q(.U) q(Nat)
#eval getTmₛ (u := .zero) [``Nat] q(Nₛ) q(.U) q(Nat) >>= inferType
#eval getTmₛ (u := .zero) [``Vec] q(Vₛ) q(.U) q(Vec 123)
-- #eval getTmₛ (u := .zero) [``Vec] q(Vₛ) q(.U) q(Vec 123)

#exit

/-- Parse a constructor type, for example `(n : Nat) -> Even n -> Odd (n+1)`. -/
partial def getTyₚ (mblock : List Name) (Γₛ : Q(Conₛ.{u})) (tys : Expr) : MetaM Q(Tyₚ.{u} $Γₛ) := do
  forallBoundedTelescope tys (some 1) fun var body => do
    if var.isEmpty then -- `El T`
      let T <- getTmₛ Γₛ q(Tyₛ.U.{u}) body
      return q(Tyₚ.El.{u} $T)
    else -- PFunc or PPi
      let var := var[0]!
      let ty : Q(Type u) <- var.fvarId!.getType
      let .const tyF _ := ty.getAppFn | throwError "getTyₚ parameter {ty}"
      if mblock.contains tyF then -- PFunc
        let T : Q(Tmₛ.{u} $Γₛ Tyₛ.U) <- getTmₛ Γₛ q(Tyₛ.U.{u}) ty
        let rest <- getTyₚ mblock Γₛ body
        return q(Tyₚ.PFunc.{u} $T $rest)
      else -- PPi
        let rest : Q($ty -> Tyₚ.{u} $Γₛ) <- getTyₚ mblock Γₛ body
        return q(Tyₚ.PPi.{u} $ty $rest)

partial def getConₛ (block : InductiveVal) : MetaM Q(Conₛ.{u}) := do
  block.all.foldlM (fun (acc : Q(Conₛ.{u})) I => do
    let info <- getConstInfoInduct I
    let ty : Q(Tyₛ.{u}) <- getTyₛ info.type
    return q(Conₛ.ext $acc $ty)
  ) q(Conₛ.nil.{u})

partial def getConₚ (block : InductiveVal) (Γₛ : Q(Conₛ.{u})) : MetaM Q(Conₚ.{u} $Γₛ) := do
  let allCtors : List Name <- block.all.foldlM (fun (acc : List Name) I => do
    let info <- getConstInfoInduct I
    return info.ctors ++ acc
  ) []
  allCtors.foldlM (fun (acc : Q(Conₚ.{u} $Γₛ)) c => do
    let info <- getConstInfoCtor c
    let ty <- getTyₚ block.all Γₛ info.type
    return q(Conₚ.ext $acc $ty)
  ) q(Conₚ.nil.{u})

elab "getConₛ! " i:ident : term => do
  let ind <- getConstInfoInduct i.getId
  let u <- mkFreshLevelMVar
  getConₛ (u := u) ind

#check Vec
#check getConₛ! Vec

partial def skipParams (tys : Expr) (nParams : Nat) (cont : Expr -> MetaM Expr) : MetaM Expr :=
  match nParams with
  | 0 => cont tys
  | nParams + 1 => do
    forallBoundedTelescope tys (some 1) fun var body => do
      let body' <- skipParams body nParams cont
      if body'.containsFVar var[0]!.fvarId! then mkLambdaFVars var body'
      else return body'

elab "getTyₛ! " tys:term : term => do
  let tys <- elabTerm tys none
  let u <- mkFreshLevelMVar
  getTyₛ (u:=u) tys

elab "Tyₛ% " T:term : term => do
  let T <- elabTerm T none
  let ⟨I, args⟩ := T.getAppFnArgs
  let info <- getConstInfoInduct I
  if info.numParams != args.size then throwError m!"Expected {info.numParams} params."
  let u <- mkFreshLevelMVar
  skipParams info.type info.numParams (getTyₛ (u := u))

elab "Conₛ% " T:term : term => do
  let T <- elabTerm T none
  let ⟨I, args⟩ := T.getAppFnArgs
  let info <- getConstInfoInduct I
  if info.numParams != args.size then throwError m!"Expected {info.numParams} params."
  let u <- mkFreshLevelMVar
  getConₛ (u := u) info

elab "Conₚ% " T:term : term => do
  let T <- elabTerm T none
  let ⟨I, args⟩ := T.getAppFnArgs
  let info <- getConstInfoInduct I
  if info.numParams != args.size then throwError m!"Expected {info.numParams} params."
  let u <- mkFreshLevelMVar
  getConₛ (u := u) info

elab "%Tyₚ " i:ident : term => do
  let ind <- getConstInfoInduct i.getId
  getTyₚ ind.all

mutual
  inductive Even : Nat -> Type
  | zero : Even 0
  | even : Odd n -> Even (n+1)
  inductive Odd : Nat -> Type
  | odd : Even n -> Odd (n+1)
end

#check getTyₛ! (Nat -> Type)
#check Tyₛ% (Vec String)
#check Conₛ% (Vec String)
#check Conₛ% (Even)
-- example

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

elab "%Tyₚ " i:ident : term => do
  let ind <- getConstInfoInduct i.getId
  getTyₚ ind.type

#check Vec
#check %Tyₛ Vec
