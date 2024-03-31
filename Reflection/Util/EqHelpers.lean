
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.28h.E2.82.82.20.E2.96.B8.20h.E2.82.81.29.20.E2.96.B8.20x.20.3D.20h.E2.82.82.20.E2.96.B8.20.28h.E2.82.81.20.E2.96.B8.20x.29/near/411362225 wow this URL
theorem eq_cast_trans  (h₁ : A = B) (h₂ : B = C) (x : A)
  : h₂ ▸ h₁ ▸ x = (h₂ ▸ h₁) ▸ x
  := by cases h₁; cases h₂; rfl

theorem eq_symm_cancel {T : I -> Type u} {a b : I} (h : a = b) (x : T b)
  : h ▸ h.symm ▸ x = x
  := by cases h; rfl

/-- Universe-polymorphic version of `forall_congr`. Thanks Arthur! -/
theorem forall_pcongr {α : Sort u} {p q : α → Sort v} (h : ∀ a, p a = q a) : (∀ a, p a) = (∀ a, q a) :=
  (funext h : p = q) ▸ rfl
