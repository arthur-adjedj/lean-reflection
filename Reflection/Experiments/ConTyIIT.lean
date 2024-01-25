import Lean -- not essential: only for `Lean.Meta.getEqnsFor?` later

/-
  Example from section 7.1 of http://von-raumer.de/academic/phd_vonraumer.pdf .
  Note: Non-dependent eliminator.
-/

set_option pp.proofs true
set_option linter.unusedVariables false

theorem eq_symm_cancel {T : I -> Type _} {a b : I} (h : a = b) (x : T b) : h ▸ h.symm ▸ x = x
  := by cases h; rfl

-- # Syntax

mutual
  inductive ETyₛ : Type 1
  | U : EConₛ -> ETyₛ
  /-- `Γₛ ⊢ dom` and `Γₛ,x:dom ⊢ body` therefore `Γₛ ⊢ (x : dom) -> body`. -/
  | Pi : EConₛ -> (dom : ETyₛ) -> (body : ETyₛ) -> ETyₛ

  inductive EConₛ
  | nil : EConₛ
  | ext : EConₛ -> ETyₛ -> EConₛ
end

mutual
  inductive WConₛ : EConₛ -> Prop
  | nil : WConₛ .nil
  | ext : WConₛ Γₛ -> WTyₛ Γₛ Aₛ -> WConₛ (EConₛ.ext Γₛ Aₛ)

  inductive WTyₛ : EConₛ -> ETyₛ -> Prop
  | U : WConₛ Γₛ -> WTyₛ Γₛ (ETyₛ.U Γₛ)
  | Pi : WConₛ Γₛ -> WTyₛ Γₛ Aₛ -> WTyₛ (EConₛ.ext Γₛ Aₛ) Bₛ -> WTyₛ Γₛ (ETyₛ.Pi Γₛ Aₛ Bₛ)
end

structure Conₛ : Type 1 where
  e : EConₛ
  w : WConₛ e

structure Tyₛ (Γₛ : Conₛ) : Type 1 where
  e : ETyₛ
  w : WTyₛ Γₛ.e e

def nilₛ : Conₛ                                                   := ⟨EConₛ.nil, WConₛ.nil⟩
def extₛ (Γₛ : Conₛ) (Aₛ : Tyₛ Γₛ) : Conₛ                         := ⟨EConₛ.ext Γₛ.e Aₛ.e, WConₛ.ext Γₛ.w Aₛ.w⟩
def U (Γₛ : Conₛ) : Tyₛ Γₛ                                        := ⟨ETyₛ.U Γₛ.e, WTyₛ.U Γₛ.w⟩
def Piₛ (Γₛ : Conₛ) (A : Tyₛ Γₛ) (B : Tyₛ (extₛ Γₛ A)) : Tyₛ Γₛ   := ⟨ETyₛ.Pi Γₛ.e A.e B.e, WTyₛ.Pi Γₛ.w A.w B.w⟩

-- ## Eliminator construction
-- Okay great we have those four "constructors" now... but how do we actually get an eliminator?
-- Can't do this, since `nilₛ` is a function and not a ctor:
-- def recCon {n : C} : Conₛ -> C
-- | .nilₛ => n
-- | .extₛ Γₛ Aₛ => e ...

-- Dependent eliminator would have needed the following:
-- variable {C : Conₛ -> Type _} {T : {Γ : Conₛ} -> C Γ -> Tyₛ -> Type _}

variable {C : Type _} {T : C -> Type _}
variable (n : C)
variable (e : (γ : C) -> T γ -> C)
variable (u : (γ : C) -> T γ)
variable (p : (γ : C) -> (a : T γ) -> T (e γ a) -> T γ)

mutual
  inductive RConₛ : EConₛ -> C -> Prop
  | nil : RConₛ EConₛ.nil n
  | ext : RConₛ Γₛ γ -> RTyₛ Aₛ a -> RConₛ (EConₛ.ext Γₛ Aₛ) (e γ a)
  inductive RTyₛ : ETyₛ -> {γ : C} -> T γ -> Prop
  | U : RConₛ Γₛ γ -> RTyₛ (ETyₛ.U Γₛ) (u γ)
  | Pi : RConₛ Γₛ γ -> RTyₛ Aₛ a -> RTyₛ Bₛ b -> RTyₛ (ETyₛ.Pi Γₛ Aₛ Bₛ) (p γ a b)
end

mutual
  theorem RConₛ_right_unique {γ γ' : C} : {Γₛ : EConₛ} -> RConₛ n e u p Γₛ γ -> RConₛ n e u p Γₛ γ' -> γ = γ'
  | .nil, h, h' => by cases h; cases h'; rfl
  | .ext Γₛ Aₛ, .ext rΓₛ rAₛ, .ext rΓₛ' rAₛ' => by
    cases RConₛ_right_unique rΓₛ rΓₛ'
    cases RTyₛ_right_unique rAₛ rAₛ'
    rfl
  theorem RTyₛ_right_unique {γ : C} {a a' : T γ} : {Aₛ : ETyₛ} -> RTyₛ n e u p Aₛ a -> RTyₛ n e u p Aₛ a' -> a = a'
  | .U Γₛ, h, h' => by cases h; cases h'; rfl
  | .Pi _ Aₛ Bₛ, .Pi _ rAₛ rBₛ, .Pi _ rAₛ' rBₛ' => by
    cases RTyₛ_right_unique rAₛ rAₛ'
    cases RTyₛ_right_unique rBₛ rBₛ'
    rfl
end

mutual
  def RConₛ_left_total : (Γₛ : EConₛ) -> WConₛ Γₛ -> (γ : C) ×' RConₛ n e u p Γₛ γ
  | .nil      , _ => ⟨n, .nil⟩
  | .ext Γₛ Aₛ, w =>
    have ⟨γ, rγ⟩ := RConₛ_left_total Γₛ (let .ext wΓₛ _wAₛ := w; wΓₛ)
    have ⟨a, ra⟩ := RTyₛ_left_total Aₛ (let .ext _wΓₛ wAₛ := w; wAₛ) γ rγ
    ⟨e γ a, RConₛ.ext rγ ra⟩
  def RTyₛ_left_total : {Γₛ : EConₛ} -> (Aₛ : ETyₛ) -> WTyₛ Γₛ Aₛ -> (γ : C) -> RConₛ n e u p Γₛ γ -> (a : T γ) ×' RTyₛ n e u p Aₛ a
  | _, .U Γₛ       , w, γ, rγ => ⟨u γ, RTyₛ.U (let .U _ := w; rγ)⟩
  | Γₛ, .Pi _Γₛ Aₛ Bₛ, w, γ, rγ => by
    have : _Γₛ = Γₛ := by let .Pi wΓₛ wAₛ wBₛ := w; cases wΓₛ; rfl; rfl
    cases this
    have ⟨a, ra⟩ := RTyₛ_left_total Aₛ (let .Pi _wΓₛ wAₛ _wBₛ := w; wAₛ) γ rγ
    have ⟨b, rb⟩ := RTyₛ_left_total Bₛ (let .Pi _wΓₛ _wAₛ wBₛ := w; wBₛ) _ (RConₛ.ext rγ ra)
    exact ⟨p γ a b, RTyₛ.Pi rγ ra rb⟩
end

def recCon (Γₛ : Conₛ) : C :=
  RConₛ_left_total n e u p Γₛ.e Γₛ.w |>.fst

def recTy (Aₛ : Tyₛ Γₛ) : T (recCon n e u p Γₛ) := by
  let γ := RConₛ_left_total n e u p Γₛ.e Γₛ.w
  have : γ.fst = recCon n e u p Γₛ := by rw [recCon] -- a little ugly
  cases this
  exact RTyₛ_left_total n e u p /-Γₛ.e-/ Aₛ.e Aₛ.w γ.fst γ.snd |>.fst

theorem recCon_nil : recCon n e u p nilₛ = n := rfl

theorem recCon_ext : recCon n e u p (extₛ Γₛ Aₛ) = e (recCon n e u p Γₛ) (recTy n e u p Aₛ) := by
  let lhs := RConₛ_left_total n e u p (extₛ Γₛ Aₛ).e (extₛ Γₛ Aₛ).w -- lhs_r : RConₛ (extₛ Γₛ Aₛ).e lhs
  let rhs_γ := RConₛ_left_total n e u p Γₛ.e Γₛ.w
  let rhs_a := RTyₛ_left_total n e u p Aₛ.e Aₛ.w rhs_γ.fst rhs_γ.snd -- r_rhs_a : RTyₛ Aₛ.e rhs_a
  let rhs := e rhs_γ.fst rhs_a.fst
  simp [extₛ] at lhs

  have r_rhs : RConₛ n e u p (extₛ Γₛ Aₛ).e rhs := RConₛ.ext rhs_γ.snd rhs_a.snd
  have eq_lhs   : recCon n e u p (extₛ Γₛ Aₛ) = lhs.fst := by rw [recCon]
  have eq_rhs_γ : recCon n e u p Γₛ = rhs_γ.fst := by rw [recCon]
  have eq_rhs_a : recTy  n e u p Aₛ = rhs_a.fst := by rw [recTy]
  rw [eq_lhs]
  rw [eq_rhs_a]
  have (γ γ' : C) (a : T γ) (h : γ = γ') : e γ a = e γ' (h ▸ a) := by subst h; rfl
  rw [this (recCon n e u p Γₛ) rhs_γ.fst _ eq_rhs_γ]
  have eq : lhs.fst = rhs := RConₛ_right_unique n e u p lhs.snd r_rhs
  exact eq

theorem recTy_U : recTy n e u p (U Γₛ) = u (recCon n e u p Γₛ) := by
  let γ := RConₛ_left_total n e u p Γₛ.e Γₛ.w

  let lhs := RTyₛ_left_total n e u p (U Γₛ).e (U Γₛ).w γ.fst γ.snd
  have eq_lhs : recTy n e u p (U Γₛ) = lhs.fst := by rw [recTy]
  rw [eq_lhs]

  let rhs_γ := RConₛ_left_total n e u p Γₛ.e Γₛ.w
  have eq_rhs_γ : recCon n e u p Γₛ = rhs_γ.fst := by rw [recCon]
  have (γ γ') (h : γ' = γ): u γ = h ▸ u γ' := by subst h; rfl
  rw [this (recCon n e u p Γₛ) γ.fst eq_rhs_γ] -- just `rw [eq_rhs_γ]` wouldn't have worked

  -- let rhs := u rhs_γ.fst
  let r_rhs := RTyₛ.U rhs_γ.snd
  let eq := RTyₛ_right_unique n e u p lhs.snd r_rhs
  exact eq

theorem recTy_Pi
  : recTy n e u p (Piₛ Γₛ Aₛ Bₛ)
  = p (recCon n e u p Γₛ) (recTy n e u p Aₛ) (recCon_ext n e u p ▸ recTy n e u p Bₛ)
:= by
  let γ := RConₛ_left_total n e u p Γₛ.e Γₛ.w
  have reduces_γ : recCon n e u p Γₛ = γ.fst := by rw [recCon]
  -- rw [reduces_γ]

  let lhs := RTyₛ_left_total n e u p (Piₛ Γₛ Aₛ Bₛ).e (Piₛ Γₛ Aₛ Bₛ).w γ.fst γ.snd
  have reduces_lhs : recTy n e u p (Piₛ Γₛ Aₛ Bₛ) = lhs.fst := by rw [recTy]
  rw [reduces_lhs]

  let a := RTyₛ_left_total n e u p Aₛ.e Aₛ.w γ.fst γ.snd
  have reduces_a : recTy n e u p Aₛ = a.fst := by rw [recTy]

  let eγa := RConₛ_left_total n e u p (extₛ Γₛ Aₛ).e (extₛ Γₛ Aₛ).w -- used in the type of B
  -- have reduces_EΓA_to_eγa : recCon n e u p (extₛ Γₛ Aₛ) = eγa.fst := by rw [recCon]
  have reduces_EΓA_to_e_γ_a : recCon n e u p (extₛ Γₛ Aₛ) = e γ.fst a.fst := by
    rw [recCon_ext]
    apply congrArg
    exact reduces_a
  -- have reduces_EΓA_to_e_γ'_a' : recCon n e u p (extₛ Γₛ Aₛ) = e (recCon n e u p Γₛ) (recTy n e u p Aₛ)
  --   := by rw [recCon_ext n e u p]
  -- have reduces_e_γ_a_to_eγa : eγa.fst = e γ.fst a.fst := reduces_EΓA_to_e_γ_a ▸ reduces_EΓA_to_eγa
  have h_e_γ_a (γ γ' : C) (a : T γ) (hγ : γ = γ') : e γ a = e γ' (hγ ▸ a) := by subst hγ; rfl
  -- rw [reduces_eγa] fails

  let b' := RTyₛ_left_total n e u p Bₛ.e Bₛ.w (recCon n e u p (extₛ Γₛ Aₛ)) eγa.snd
  -- have reduces_b' : recTy n e u p Bₛ = b'.fst := by
  --   rw [recTy]
  --   sorry
  --   done

  let b'' := RTyₛ_left_total n e u p Bₛ.e Bₛ.w eγa.fst eγa.snd
  have reduces_b'' : recTy n e u p Bₛ = b''.fst := by rw [recTy]

  let b := RTyₛ_left_total n e u p Bₛ.e Bₛ.w (e γ.fst a.fst) (.ext γ.snd a.snd)
  have reduces_b : recTy n e u p Bₛ = recCon_ext n e u p ▸ b.fst := by
    -- rw [reduces_b']
    have := h_e_γ_a
    have := b'.snd
    have := b.snd
    -- have (h : RTyₛ n e u p Bₛ.e b.fst) : Eq.symm (recCon_ext n e u p) ▸ b.fst := by sorry
    -- have : e γ.fst a.fst = recCon n e u p (extₛ Γₛ Aₛ) := sorry

    have helper
      (eγa eγa' : C) (h_eγa : eγa = eγa')
      (b : T eγa) (b' : T eγa') (hb : b = h_eγa ▸ b')
      : @RTyₛ C T n e u p Bₛ.e eγa  b
      = @RTyₛ C T n e u p Bₛ.e eγa' b'
      := by subst h_eγa; subst hb; rfl


    -- b.snd has type
    --     @RTyₛ C (fun γ => T γ) n e u p Bₛ.e (e γ.fst a.fst)                b.fst
    -- but expected to have
    --     @RTyₛ C (fun γ => T γ) n e u p Bₛ.e (recCon n e u p (extₛ Γₛ Aₛ)) (Eq.symm (recCon_ext n e u p) ▸ b.fst)
    have asdf : recTy n e u p Bₛ = Eq.symm (recCon_ext n e u p) ▸ b.fst
      := @RTyₛ_right_unique C T n e u p _ _ _ _ b'.snd (by
        rw [<- helper
          (e γ.fst a.fst) (recCon n e u p (extₛ Γₛ Aₛ)) (recCon_ext n e u p).symm
          b.fst (Eq.symm (recCon_ext n e u p) ▸ b.fst) (eq_symm_cancel _ _ ▸ rfl)]
        exact b.snd
        done
      )
    exact asdf

    done

  have
    (γ : C)         (γ' : C)                               (hγ : γ' = γ)
    (a : T γ)       (a' : T γ')                            (ha : a' = hγ ▸ a)
    (r_EΓA : C)
    (reduces_EΓA_e_γ_a   : r_EΓA = e γ a)
    (reduces_EΓA_e_γ'_a' : r_EΓA = e γ' a')
    (b : T (e γ a)) (b' : T r_EΓA) (hb : b' = reduces_EΓA_e_γ_a ▸ b)
    : p γ' a' (reduces_EΓA_e_γ'_a' ▸ b') = hγ ▸ p γ (hγ ▸ a) (eq_symm_cancel hγ _ ▸ b)
    := by
      subst hγ
      subst ha
      subst reduces_EΓA_e_γ'_a'
      subst hb
      rfl

  rw [this
    γ.fst (recCon n e u p Γₛ) reduces_γ
    a.fst (recTy  n e u p Aₛ) reduces_a
    (recCon n e u p (extₛ Γₛ Aₛ))
    reduces_EΓA_to_e_γ_a
    (recCon_ext n e u p)
    -- reduces_EΓA_to_e_γ'_a'
    b.fst (recTy n e u p Bₛ) (reduces_b)
  ]

  exact RTyₛ_right_unique n e u p lhs.snd (.Pi γ.snd a.snd b.snd)

def f : Conₛ -> Nat
  := recCon (C := Nat)
    0 -- n
    (fun γ t => γ + 1) -- e
    (fun γ => 1000) -- u
    (fun γ a b => 2000)

#reduce f nilₛ

def mk_large : Nat -> Conₛ
| 0 => nilₛ
| .succ n => extₛ (mk_large n) (U (mk_large n))

-- #reduce f (mk_large 6)
-- #eval f (mk_large 6000)

def ConₛA : Conₛ -> Type 1 :=
  recCon (C := Type 1) (T := fun γ => Type 1)
    PUnit
    (fun (γ : Type 1) (a : Type 1) => a × γ)
    (fun γ => Type)
    (fun γ a b => (t : a) -> b)

/-- Nat : Type -/
def Nₛ : Conₛ := extₛ nilₛ (U nilₛ)
/-- Vec : Nat -> Type -/
def Vₛ : Conₛ := extₛ nilₛ (Piₛ nilₛ (U nilₛ) (U (extₛ nilₛ (U nilₛ))))

#reduce ConₛA Nₛ
#reduce ConₛA Vₛ

def TyₛA : Tyₛ Γₛ -> Type 1 :=
  recTy (C := Type 1) (T := fun γ => Type 1)
    PUnit
    (fun (γ : Type 1) (a : Type 1) => a × γ)
    (fun γ => Type)
    (fun γ a b => (t : a) -> b)

#reduce TyₛA (U nilₛ)
#reduce TyₛA (Piₛ nilₛ (U nilₛ) (U (extₛ nilₛ (U nilₛ))))
