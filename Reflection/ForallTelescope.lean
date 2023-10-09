import Reflection.Vec

def ForallTelescope (doms : Vec (Sort u) k) (body : ((idx : Fin k) -> Get doms idx) -> Sort u) : Sort u :=
  match doms with
  | .nil => body (fun ⟨_, h⟩ => absurd h (Nat.not_lt_zero _))
  | .cons A doms' => (x : A) -> ForallTelescope doms' fun f => body fun
    | ⟨0, _h⟩ => x
    | ⟨.succ i, _h⟩ => f ⟨i, _⟩

def ForallTelescopeP (doms : Vec (Sort u) k) (body : ((idx : Fin k) -> Get doms idx) -> Prop) : Prop :=
  match doms with
  | .nil => body (fun ⟨_, h⟩ => absurd h (Nat.not_lt_zero _))
  | .cons A doms' => (x : A) -> ForallTelescopeP doms' (fun f => body (fun
    | ⟨0, _h⟩ => x
    | ⟨.succ i, _h⟩ => f ⟨i, _⟩))

#reduce ForallTelescopeP
  (Nat ::: String ::: ⟦⟧)
  (fun f => (f 0 : Nat) = (123 : Nat) /\ f 1 = "Foo")

#reduce ForallTelescopeP
  (Int ::: String ::: ⟦⟧)
  (fun f => f 1 = f 1 /\ f 0 = f 0)

#reduce ForallTelescope
  (Type ::: ⟦⟧)
  (fun f => Vec (f 0) 2)

#reduce ForallTelescope
  (ULift.{1, 1} Type ::: ULift.{1, 0} Nat ::: ⟦⟧)
  (fun f => Vec (ULift.down <| f 0) (ULift.down <| f 1))

-- def ForallTelescoper (doms : Vec (Prop -> Prop) k) (body : ((idx : Fin k) -> Get doms idx) -> Sort 0) : Sort 0 :=
--   match doms with
--   | .nil => body (fun ⟨_, h⟩ => absurd h (Nat.not_lt_zero _))
--   | .cons domer doms' =>
--     let inner := ForallTelescopeP doms' fun f => body fun
--       | ⟨0, _h⟩ => x
--       | ⟨.succ i, _h⟩ => f ⟨i, _⟩
--     domer inner