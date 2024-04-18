-- import Aesop

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.28h.E2.82.82.20.E2.96.B8.20h.E2.82.81.29.20.E2.96.B8.20x.20.3D.20h.E2.82.82.20.E2.96.B8.20.28h.E2.82.81.20.E2.96.B8.20x.29/near/411362225 wow this URL
-- @[aesop unsafe]
theorem eq_cast_trans  (h₁ : A = B) (h₂ : B = C) (x : A)
  : h₂ ▸ h₁ ▸ x = (h₂ ▸ h₁) ▸ x
  := by cases h₁; cases h₂; rfl

-- @[aesop unsafe]
theorem Eq.cast_trans_dep {I} {T : I -> Sort _} {i₁ i₂ i₃ : I} (h₂ : i₂ = i₃) (h₁ : i₁ = i₂) (h₃ : i₁ = i₃) (x : T i₁)
    : h₂ ▸ h₁ ▸ x = h₃ ▸ x
    := by cases h₁; rfl

-- @[aesop unsafe]
theorem Eq.apply_u {A : T -> Sort _} {f g : (u:T) -> A u} : f = g -> (u : T) -> f u = g u := by
  intro h u; cases h; rfl

-- @[aesop unsafe]
theorem Eq.cast_apply_u {A : T -> Sort _} {a₁ a₂ : (u:T) -> A u} {h : a₁ = a₂} {hu : (u : T) -> a₁ u = a₂ u}
  {D : (u : T) -> A u -> Sort _} {d₁ : (u : T) -> D u (a₁ u)} {d₂ : (u : T) -> D u (a₂ u)}
  : d₁ = h ▸ d₂ -> (u : T) -> d₁ u = (hu u) ▸ d₂ u := by
  intro ih u; cases h; cases ih; rfl

-- @[aesop unsafe]
theorem eq_symm_cancel {T : I -> Type u} {a b : I} (h : a = b) (x : T b)
  : h ▸ h.symm ▸ x = x
  := by cases h; rfl

/-- Universe-polymorphic version of `forall_congr`. Thanks Arthur! -/
theorem forall_pcongr {α : Sort u} {p q : α → Sort v} (h : ∀ a, p a = q a) : (∀ a, p a) = (∀ a, q a) :=
  (funext h : p = q) ▸ rfl
