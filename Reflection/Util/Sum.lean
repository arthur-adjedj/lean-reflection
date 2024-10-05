import Aesop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-- "Big sum" operator $Σ_{i = lower}^{upper - 1} f(i)$.\
  **Note the exclusive upper bound `-1`!** -/
@[aesop unsafe] def sum (lower upper : Nat) (f : (x : Nat) -> x >= lower ∧ x < upper -> Nat) : Nat :=
  if h : lower < upper then
    (f lower (by simp_all only [ge_iff_le, le_refl, and_self]))
    + sum (lower + 1) upper (fun x hx => f x (by omega))
  else 0
  termination_by 1 + upper - lower

example : sum 9 9 (fun i _ => 10 + i) = 0 := rfl
example : sum 0 1 (fun i _ => 10 + i) = (10 + 0) := rfl
example : sum 2 4 (fun i _ => 10 + i) = (10 + 2) + (10 + 3) := rfl

@[aesop unsafe] theorem sum_begin (h : lower < upper)
  : sum lower upper f = f lower (by omega) + sum (lower + 1) upper (fun x hx => f x (by omega))
  := by rw [sum]; simp_all only [↓reduceDite]
@[simp] theorem sum_zero : sum n n f = 0 := by rw [sum]; simp
@[aesop unsafe] theorem sum_end (h : lower <= upper)
  : sum lower (upper + 1) f = sum lower upper (fun x hx => f x (by omega)) + f upper (by omega)
  := by sorry
