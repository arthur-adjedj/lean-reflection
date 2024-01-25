inductive Vec (α : Sort u) : Nat -> Type u
| nil : Vec α 0
| cons : (val : α) -> Vec α k -> Vec α (k + 1)

def Vec.get {α : Sort u} : Vec α n -> Fin n -> α
| .nil      , ⟨k      , h⟩ => absurd h (Nat.not_lt_zero k)
| .cons _ xs, ⟨.succ k, h⟩ => get xs ⟨k, Nat.lt_of_succ_lt_succ h⟩
| .cons x  _, ⟨.zero  , h⟩ => x

def Vec.map {α : Sort u} : Vec α n -> (f : α -> β) -> Vec β n
| .nil, f => .nil
| .cons x xs, f => .cons (f x) (map xs f)
