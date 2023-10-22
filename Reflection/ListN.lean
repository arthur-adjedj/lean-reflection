inductive ListN
| nil : ListN
| cons : Nat -> ListN -> ListN

#check ListN.rec
/-
  {motive : ListN → Sort u} →
  motive ListN.nil →
  ((a : Nat) → (a_1 : ListN) → motive a_1 → motive (ListN.cons a a_1)) →
  (t : ListN) →
  motive t
-/

-- We don't actually need these as theorems, since they're part of the theory directly.
-- But they're here for visualization.
theorem ListN.iota_nil (motive : ListN -> Prop)
  (case_nil : motive ListN.nil)
  (case_cons : (head : Nat) → (tail : ListN) → motive tail → motive (ListN.cons head tail))
  : @ListN.rec motive case_nil case_cons (ListN.nil) = case_nil
  := Eq.refl _

theorem ListN.iota_cons (motive : ListN -> Prop)
  (case_nil : motive ListN.nil)
  (case_cons : (head : Nat) → (tail : ListN) → motive tail → motive (ListN.cons head tail))
  (head : Nat)
  (tail : ListN)
  : @ListN.rec motive case_nil case_cons (ListN.cons head tail)
      = case_cons head tail (@ListN.rec motive case_nil case_cons tail)
  := Eq.refl _





/-
  # Rec and Iotas for Nat
  Just because too lazy to make new file for Nat.
-/

#check Nat.rec
/- {motive : Nat → Sort u} →
  motive Nat.zero →
  ((n : Nat) → motive n → motive (Nat.succ n)) →
  (t : Nat) →
  motive t
-/

theorem Nat.iota_zero (motive : Nat -> Prop)
  (case_zero : motive Nat.zero)
  (case_succ : (n : Nat) -> motive n → motive (Nat.succ n))
  : @Nat.rec motive case_zero case_succ Nat.zero = case_zero
  := Eq.refl _

theorem Nat.iota_succ (motive : Nat -> Prop)
  (case_zero : motive Nat.zero)
  (case_succ : (n : Nat) -> motive n → motive (Nat.succ n))
  (n : Nat)
  : @Nat.rec motive case_zero case_succ (Nat.succ n)
      = case_succ n (@Nat.rec motive case_zero case_succ n)
  := Eq.refl _
