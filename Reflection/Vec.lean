
inductive Vec (α : Sort u) : Nat -> Type u
| nil : Vec α 0
| cons : (val : α) -> Vec α k -> Vec α (k + 1)
  infixr:67 " ::: " => Vec.cons
  notation "⟦⟧" => Vec.nil

def xxx₃ : Vec (Type 1) 1 := (ULift.{1, 1} Type) ::: Vec.nil
def xxx₄ : Vec (Type 1) 1 := (ULift.{1, 0} Nat) ::: Vec.nil
def test : Vec (Type 1) 2 := (ULift.{1, 0} Nat) ::: (ULift.{1, 1} Type) ::: Vec.nil

abbrev Get {α : Sort u} : Vec α n -> Fin n -> α
| .nil      , ⟨k      , h⟩ => absurd h (Nat.not_lt_zero k)
| .cons _ xs, ⟨.succ k, h⟩ => Get xs ⟨k, Nat.lt_of_succ_lt_succ h⟩
| .cons x  _, ⟨.zero  , h⟩ => x

def Map {α : Sort u} : Vec α n -> (f : α -> β) -> Vec β n
| .nil, f => .nil
| .cons x xs, f => .cons (f x) (Map xs f)

#check Vec.rec
