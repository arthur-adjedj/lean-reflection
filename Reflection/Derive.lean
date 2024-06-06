import Lean
import Reflection.MutualInductive
import Qq

open Lean Meta Elab Term Qq
open Reflection MutualInductive

set_option pp.fieldNotation.generalized false

namespace Reflection.MutualInductive.Derive

inductive Vec : Nat -> Type
| nil : Vec 0
| cons : (n : Nat) -> String -> Vec n -> Vec (n + 1)

/-- Given for example `q(Vec)`, returns its InductiveVal. -/
def resolve (T : TSyntax `term) : TermElabM InductiveVal := do
  let T := (<- elabTerm T none)
  let .const name _ := T.getAppFn | throwError "expected a simple const"
  getConstInfoInduct name

def _root_.List.indexOf [BEq α] : List α -> α -> Option Nat
| []     , _ => none
| x :: xs, a => if x == a then some 0 else (indexOf xs a).map (. + 1)



/-- Reads in `Nat -> Type`. -/
partial def getTyₛ (τ : Q(Type (u+1))) : MetaM Q(Tyₛ.{u}) := do
  forallBoundedTelescope τ (some 1) fun var body => do
    if var.isEmpty then
      -- unless <- isDefEq (<- inferType ty) q(Type u) do throwError "getTyₛ isDefEq failed\n{(<- inferType ty)} =/= {q(Type u)}"
      unless <- isDefEq body q(Type u) do throwError "getTyₛ isDefEq failed between {body} and {q(Type u)}"
      return <- instantiateMVars q(Tyₛ.U.{u})
    else
      let var := var[0]!
      let ty : Q(Type u) <- var.fvarId!.getType -- for example `ty ≣ Nat`
      unless <- isDefEq (<- inferType ty) q(Type u) do throwError "getTyₛ isDefEq failed\n{(<- inferType ty)} =/= {q(Type u)}"
      let rest : Q(Tyₛ.{u}) <- getTyₛ body -- rest is for example `var : X ⊢ SPi ...`
      let rest : Q($ty -> Tyₛ.{u}) <- mkLambdaFVars #[var] rest
      return <- instantiateMVars q(Tyₛ.SPi.{u} $ty $rest)

partial def getConₛ (block : InductiveVal) : MetaM Q(Conₛ.{u}) := do
  block.all.foldlM (fun (acc : Q(Conₛ.{u})) I => do
    let info <- getConstInfoInduct I
    let ty : Q(Tyₛ.{u}) <- getTyₛ info.type
    return q(Conₛ.ext $acc $ty)
  ) q(Conₛ.nil.{u})

elab "getTyₛ! " T:term:max : term => do
  getTyₛ (u := <- mkFreshLevelMVar) (<- resolve T).type
elab "getConₛ! " T:term:max : term => do
  getConₛ (u := <- mkFreshLevelMVar) (<- resolve T)

def testConₛ := getConₛ! Vec
#print testConₛ

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

/-- Reads in `Vec 123`. Make sure that `mblock` has the names of `Γₛ` in the same order. -/
partial def getTmₛ (mblock : List Name) (Γₛ : Q(Conₛ.{u})) (Aₛ : Q(Tyₛ.{u})) (T : Q(TyₛA.{u, u} $Aₛ)) : MetaM Q(Tmₛ.{u} $Γₛ $Aₛ) := do
  let T : Q(TyₛA.{u, u} $Aₛ) <- whnf T
  match T with
  | .const name _ =>
    let some idx := mblock.indexOf name | throwError "getTmₛ case Tyₛ.U: {T} does not belong to mutual block {mblock}"
    let var <- getVarₛ idx Γₛ Aₛ
    return q(Tmₛ.var $var)
  | .app f x => -- case `Vec 123 : TyₛA Aₛ`
    let ⟨u', ⟨X, x⟩⟩ <- inferTypeQ x -- x : X
    unless <- isLevelDefEq (.succ u) u' do throwError "getTmₛ level defeq failed, u ≣ {u}, but u' ≣ {u'}, with X ≣ {X}"
    let Bₛ : Q($X -> Tyₛ.{u}) <- mkFreshExprMVarQ q($X -> Tyₛ.{u})
    let fTy <- inferType f -- q(Nat -> Type)
    let fTy_code : Q(Tyₛ.{u}) <- getTyₛ (u := u) fTy -- q("Nat -> Type")
    let fTy_code_A : Q(Type (u+1)) := q(TyₛA.{u,u} $fTy_code) -- q("Nat -> Type"ᴬ) ≣ fTy ≣ q(Nat -> "Type"ᴬ)
    unless <- isDefEq fTy_code_A fTy do throwError "getTmₛ defeq failed, (TyₛA ∘ getTyₛ) doesn't roundtrip somehow\nfTy ≣ {fTy}\nfTy_code_A ≣ {fTy_code_A}"
    unless <- isDefEq fTy_code_A q((x : $X) -> TyₛA.{u,u} ($Bₛ x)) do throwError "getTmₛ defeq failed \nfTy ≣ {fTy}\nexpected ≣ {q((x : $X) -> TyₛA.{u,u} ($Bₛ x))}"
    unless <- isDefEq Aₛ q($Bₛ $x) do throwError "getTmₛ defeq failed\nAₛ ≣ {Aₛ}\nBₛ x ≣ {q($Bₛ $x)}"
    let f : Q((x : $X) -> TyₛA.{u,u} ($Bₛ $x)) := f -- this is okay because of the defeq checks above
    let fTm /-: Q(Tmₛ $Γₛ (Tyₛ.SPi $X $Bₛ))-/ <- getTmₛ mblock Γₛ (mkApp2 q(Tyₛ.SPi.{u}) X Bₛ) f
    let ret := mkAppN q(@Tmₛ.app.{u}) #[Γₛ, X, Bₛ, fTm, x]
    let ret <- instantiateMVars ret
    return ret
  | _ => throwError "oh no, getTmₛ {T}"

elab "getTmₛ! " T:term:max : term => do
  let ind <- resolve T
  let T <- elabTerm T none
  getTmₛ (u := <- mkFreshLevelMVar) ind.all (<- getConₛ ind) (<- getTyₛ (<- inferType T)) T

namespace Test
  set_option linter.unusedVariables false
  inductive AA : Nat -> Type
  | aa : AA 44
  | aaa : AA n

  inductive TT : (n : Nat) -> AA n -> Type
  | cc : (n : Nat) -> Fin n -> TT 44 .aa
  | ccc : (n : Nat) -> TT (.succ n) .aaa -> TT n .aaa

  example : Tmₛ (⬝ ▹ Tyₛ.SPi Nat fun n => Tyₛ.SPi (AA n) fun a => Tyₛ.U) (Tyₛ.SPi Nat fun n => Tyₛ.SPi (AA n) fun a => Tyₛ.U)
    := getTmₛ! TT
  example : Tmₛ (⬝ ▹ Tyₛ.SPi Nat fun n => Tyₛ.SPi (AA n) fun a => Tyₛ.U) ((fun n => Tyₛ.SPi (AA n) fun a => Tyₛ.U) 44)
    := getTmₛ! (TT 44)
  example : Tmₛ (⬝ ▹ Tyₛ.SPi Nat fun n => Tyₛ.SPi (AA n) fun a => Tyₛ.U) ((fun a => Tyₛ.U) AA.aa)
    := getTmₛ! (TT 44 .aa)
  example := getTmₛ! Vec
  example := getTmₛ! (Vec 123)
end Test

/-- Parse a constructor type, for example `(n : Nat) -> Even n -> Odd (n+1)`. -/
partial def getTyₚ (mblock : List Name) (Γₛ : Q(Conₛ.{u})) (tys : Expr) : MetaM Q(Tyₚ.{u} $Γₛ) := do
  forallBoundedTelescope tys (some 1) fun var body => do
    if var.isEmpty then -- `El T`
      let T <- getTmₛ mblock Γₛ q(Tyₛ.U.{u}) body
      return q(Tyₚ.El.{u} $T)
    else -- PFunc or PPi
      let var := var[0]!
      let ty : Q(Type u) <- var.fvarId!.getType
      let .const tyF _ := ty.getAppFn | throwError "getTyₚ parameter {ty}"
      if mblock.contains tyF then -- PFunc
        let T : Q(Tmₛ.{u} $Γₛ Tyₛ.U) <- getTmₛ mblock Γₛ q(Tyₛ.U.{u}) ty
        let rest <- getTyₚ mblock Γₛ body
        return q(Tyₚ.PFunc.{u} $T $rest)
      else -- PPi
        let rest : Q(Tyₚ.{u} $Γₛ) <- getTyₚ mblock Γₛ body
        let rest : Q($ty -> Tyₚ.{u} $Γₛ) <- mkLambdaFVars #[var] rest
        return q(Tyₚ.PPi.{u} $ty $rest)

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

elab "getTyₚ! " ctor:term:max : term => do
  let .const name _ <- Expr.getAppFn <$> elabTerm ctor none | throwError "{ctor} is not a constant"
  let ctorInfo <- getConstInfoCtor name
  let indInfo <- getConstInfoInduct ctorInfo.induct
  getTyₚ (u := <- mkFreshLevelMVar) indInfo.all (<- getConₛ indInfo) ctorInfo.type
elab "getConₚ! " T:term:max : term => do
  let T <- resolve T
  getConₚ (u := <- mkFreshLevelMVar) T (<- getConₛ T)

#check getTyₚ! Vec.nil
#check getTyₚ! Vec.cons

namespace Test
  mutual
    inductive Even : Nat -> Type
    | zero : Even 0
    | even : Odd n -> Even (n+1)
    inductive Odd : Nat -> Type
    | odd : Even n -> Odd (n+1)
  end
  #check getTyₚ! Even.zero
  #check getTyₚ! Even.even
  #check getTyₚ! Odd.odd
  #check getConₚ! Even
  #check getConₚ! Odd
  example : getConₚ! Even = getConₚ! Odd := rfl
  example := getTyₚ! Even.zero
  example := getTyₚ! Even.even
  example := getTyₚ! Odd.odd
  example := getConₚ! Even
  example := getConₚ! Odd

  #check getTyₚ! TT.ccc
  #check getTyₚ! TT.cc
  example := getTyₚ! TT.cc
  example := getTyₚ! TT.ccc
  example := getTyₚ! Vec.nil
  example := getTyₚ! Vec.cons
  example := getConₚ! TT
  example := getConₚ! Vec
end Test
