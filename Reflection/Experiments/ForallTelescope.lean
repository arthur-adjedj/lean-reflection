import Reflection.Util.Vec

def ForallTelescope (doms : Vec (Sort u) k) (body : ((idx : Fin k) -> Vec.get doms idx) -> Type (max u v)) : Type (max u v) :=
  match doms with
  | .nil => body fun ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)
  | .cons A doms' => (x : A) -> ForallTelescope doms' fun f => body fun
    | ⟨0, _h⟩ => x
    | ⟨.succ i, _h⟩ => f ⟨i, _⟩

def ForallTelescopeP (doms : Vec (Sort u) k) (body : ((idx : Fin k) -> Vec.get doms idx) -> Prop) : Prop :=
  match doms with
  | .nil => body (fun ⟨i, h⟩ => absurd h (Nat.not_lt_zero i))
  | .cons A doms => (x : A) -> ForallTelescopeP doms (fun f => body (fun
    | ⟨.zero  , _h⟩ => x
    | ⟨.succ i, _h⟩ => f ⟨i, _⟩))

#reduce ForallTelescopeP
  (Vec.cons Nat (Vec.cons String .nil))
  (fun f => (f 0 : Nat) = (123 : Nat) /\ f 1 = "Foo")

#reduce ForallTelescopeP
  (Vec.cons Int (Vec.cons String .nil))
  (fun f => f 1 = f 1 /\ f 0 = f 0)

-- #reduce ForallTelescope
--   (Vec.cons Type .nil)
--   (fun f => Vec (f 0) 2)

#reduce ForallTelescope
  (.cons (ULift.{1, 1} Type) <| .cons (ULift.{1, 0} Nat) .nil)
  (fun f => Vec (ULift.down <| f 0) (ULift.down <| f 1))

-- def ForallTelescoper (doms : Vec (Prop -> Prop) k) (body : ((idx : Fin k) -> Get doms idx) -> Sort 0) : Sort 0 :=
--   match doms with
--   | .nil => body (fun ⟨_, h⟩ => absurd h (Nat.not_lt_zero _))
--   | .cons domer doms' =>
--     let inner := ForallTelescopeP doms' fun f => body fun
--       | ⟨0, _h⟩ => x
--       | ⟨.succ i, _h⟩ => f ⟨i, _⟩
--     domer inner
