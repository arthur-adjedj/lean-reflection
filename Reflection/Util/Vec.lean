import Lean
import Qq

inductive Vec (α : Type u) : Nat -> Type u
| nil : Vec α 0
| cons : (val : α) -> Vec α k -> Vec α (k + 1)
deriving Repr

def Vec.get {α : Type u} : Vec α n -> Fin n -> α
| .nil      , ⟨k      , h⟩ => absurd h (Nat.not_lt_zero k)
| .cons _ xs, ⟨.succ k, h⟩ => get xs ⟨k, Nat.lt_of_succ_lt_succ h⟩
| .cons x  _, ⟨.zero  , h⟩ => x

def Vec.map {α : Type u} : Vec α n -> (f : α -> β) -> Vec β n
| .nil, f => .nil
| .cons x xs, f => .cons (f x) (map xs f)

open Lean Qq Meta Elab in def elabVec (α : Q(Type u)) (n : Q(Nat)) (stx : TSyntaxArray `term) : TermElabM Q(Vec $α $n) := do
  let ⟨_, vec⟩ <- stx.foldlM (fun ⟨len, vec⟩ r => do
    let r <- elabTermEnsuringTypeQ r q($α)
    return ⟨len+1, q(@Vec.cons _ _ $r $vec)⟩
  ) (⟨0, q(@Vec.nil $α)⟩ : (len : Nat) × Q(Vec $α $len))
  -- unless <- isDefEq q($len) n do throwError "expected {q(Vec $α $n)}, but got {q(Vec $α $len)}"
  return vec

open Lean Meta Elab Term Qq in
elab "⟪" xs:term,* "⟫" : term => do
  let u <- mkFreshLevelMVar
  let α <- mkFreshExprMVarQ q(Type $u)
  let n <- mkFreshExprMVarQ q(Nat)
  let v <- elabVec (u := u) α n xs.getElems
  return v


def Vec.elementWise : {n : Nat} -> Vec α n -> Vec α n -> (α -> α -> β) -> Vec β n
| 0, _, _, _ => .nil
| _+1, .cons a v, .cons b w, f => .cons (f a b) (elementWise v w f)

def Vec.fold : Vec α n -> β -> (f : α -> β -> β) -> β
| .nil, b, f => b
| .cons a v, b, f => f a (fold v b f)
