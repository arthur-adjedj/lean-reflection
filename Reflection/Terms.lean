import Aesop
import Reflection.Util.Vec
import Reflection.Util.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
-- set_option pp.fieldNotation.generalized false

-- move to own util file later:
@[aesop safe, simp] theorem Fin.add_val_pull {n : Fin (N + 1)} : n < N -> @Fin.val (N + 1) (n + 1) = (@Fin.val (N + 1) n) + 1 := by
  intro h
  rw [Fin.val_add_one_of_lt]
  simp only [Nat.succ_eq_add_one, implies_true]
  exact h

mutual
  @[aesop unsafe]
  inductive ECon : Type
  | nil : ECon
  | ext : ECon -> ETy -> ECon
  deriving Repr, Inhabited

  /-- `Ty : Con -> Type` -/
  @[aesop unsafe]
  inductive ETy : Type
  /-- `U Γ : Ty Γ` -/
  | U : ECon -> ETy
  /-- `El {Γ} : (t : Tm Γ U) -> Ty Γ` -/
  | El : ECon -> ETm -> ETy
  /-- `Pi {Γ} : (A : Ty Γ) -> (B : Ty (Γ, A)) -> Ty Γ` -/
  | Pi : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> ETy
  deriving Repr, Inhabited

  /-- `Var : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop unsafe]
  inductive EVar : Type
  /-- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]`, note that `wki : (Γ, A) <- Γ`, and `@wki Γ A = wkn (Γ, A) 1`, and `wki = wk id`. -/
  | vz : (Γ : ECon) -> (A : ETy) -> EVar
  /-- `vs {Γ} ~~{A : Ty Γ}~~ {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]`, but note that `wki` is a shorthand for `wkn (Γ, B) 1 : (Γ, B) <- Γ` -/
  | vs : (Γ : ECon) -> (B : ETy) -> EVar -> EVar
  deriving Repr, Inhabited

  /-- `Tm : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop unsafe]
  inductive ETm : Type
  /-- `var {Γ} ~~{A : Ty Γ}~~ : Var Γ A -> Tm Γ A` -/
  | var : (Γ : ECon) -> EVar -> ETm
  /-- `app {Γ : Con} {A : Ty Γ} {B : Ty (Γ, A)} : (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[id, a]`.\
    Note that the substitution `(id, a) : Γ <- (Γ, A)` intuitively instantiates de-Brujin variable #0 with `a : Tm Γ A`.  -/
  | app : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> (f : ETm) -> (a : ETm) -> ETm
  /-- `lam {Γ} {A : Ty Γ} {B : Ty (Γ, A)} : (body : Tm (Γ, A) B) -> Tm Γ (Pi A B)` -/
  | lam : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> (body : ETm) -> ETm
  /-- Only necessary because of substVarE. Will be proven impossible in the final IIRT. -/
  | error : ETm
  deriving Repr, Inhabited

  /-- A substitution `σ : Γ <- Δ` maps every variable in `Δ` to a `Γ`-term.
    Intuitively, it is a list of length `Δ.length` storing terms typed in context `Γ`. -/
  @[aesop unsafe]
  inductive ESubst : Type
  /-- `Subst.nil {Γ} : Γ <- ⬝` -/
  | nil : (Γ : ECon) -> ESubst
  /-- `Subst.cons {Γ} {Δ} {A : Ty Δ} : (δ : Γ <- Δ) -> (t : Tm Γ A[δ]) -> (Γ <- (Δ, A))` -/
  | cons : (Γ : ECon) -> (Δ : ECon) -> (A : ETy) -> ESubst -> ETm -> ESubst
  deriving Repr, Inhabited
end

@[aesop unsafe] def ECon.len : ECon -> Nat
| .nil => 0
| .ext Γ A => 1 + Γ.len
notation "∣" Γ:60 "∣" => ECon.len Γ

@[aesop unsafe] def EVar.idxΓ : EVar -> ECon
| .vz Γ .. => Γ
| .vs Γ .. => Γ

/-- Variables are de-Brujin variables. Given `.vs (.vs .vz)`, return `2`. -/
@[aesop unsafe] def EVar.deBrujin : EVar -> Nat
| .vz .. => 0
| .vs _ _ v => 1 + v.deBrujin

-- This is not provable, because `v.Γ` is arbitrary, since it is not constrained by type indices in the erased version:
-- @[aesop unsafe] theorem EVar.h_val : (v : EVar) -> v.val < ∣v.Γ∣
-- | .vz .. => ...
-- | .vs _ _ _ v => ...

@[aesop unsafe] def ESubst.len : ESubst -> Nat
| .nil Γ => 0
| .cons Γ Δ A σ t => 1 + σ.len
notation "∣" σ:60 "∣" => ESubst.len σ
example : ∣ESubst.nil Γ∣ = 0 := ESubst.len.eq_1 Γ -- doesn't work by rfl :(

@[aesop unsafe] def ESubst.Δ : ESubst -> ECon
| .nil Γ => .nil
| .cons Γ Δ A _ _ => .ext Δ A
@[aesop unsafe] def ESubst.Γ : ESubst -> ECon
| .nil Γ => Γ
| .cons Γ Δ _ _ _ => Γ

/-- Notation: `Γ ─ n`. Drop the last `n` variables in the context.
  Example: `drop (Con.nil, A, B, C) 1 ≡ (Con.nil, A, B)`. -/
@[aesop unsafe] def ECon.drop : (Γ : ECon) -> Fin (Γ.len + 1) -> ECon
| .nil    , n => .nil
| .ext Γ A, ⟨0  , h⟩ => .ext Γ A
| .ext Γ A, ⟨n+1, h⟩ => Γ.drop ⟨n, by rw [len] at h; linarith⟩
notation Γ:70 " ─ " n:70 => ECon.drop Γ n

/-- Notation: `Γᵥ`. Get the type of the de-Brujin variable `v`.
   `get : (Γ : Con) -> (v : Fin Γ.len) -> Ty (drop Γ (v+1))`. -/
@[aesop unsafe] def ECon.get : (Γ : ECon) -> (v : Fin Γ.len) -> ETy
| .nil    , v => Fin.elim0 v
| .ext Γ A, ⟨0  , h⟩ => A
| .ext Γ A, ⟨v+1, h⟩ => -- expected `Ty (drop (Γ, A) (v+1+1))`
  -- ! theorem drop_ext : drop (Γ, A) (v+1+1) = drop Γ (v+1)
  Γ.get ⟨v, by rw [len] at h; linarith⟩ -- : Ty (drop Γ (v+1))

/-- Substitutions are essentially just lists of terms. So get the term stored at position `v`. -/
def ESubst.get : (σ : ESubst) -> (v : Fin σ.len) -> ETm
| .nil Γ, v => Fin.elim0 (ESubst.len.eq_1 _ ▸ v)
| .cons _ _ _ σ t, ⟨0  , h⟩ => t
| .cons _ _ _ σ t, ⟨v+1, h⟩ => σ.get ⟨v, by rw [len] at h; linarith⟩

/-- Look up the term stored in a substitution. -/
@[aesop unsafe] def substVarE : EVar -> ESubst -> ETm
| .vz _ _  , .cons _ _ _ _ t => t
| .vs _ _ v, .cons _ _ _ σ _ => substVarE v σ
| _, _ => .error

section DecreasingMeasure
-- Bodyless definitions. Replace these and theorems about these with `variable`s later.
variable {substTyE : (Γ Δ : ECon) -> ETy -> ESubst -> ETy}
variable {substTmE : (Γ Δ : ECon) -> ETm -> ESubst -> ETm}
variable {wknE : (Γ : ECon) -> (n : Fin (∣Γ∣ + 1)) -> ESubst}
variable {mkVarE : (Γ : ECon) -> (v : Fin ∣Γ∣) -> EVar}
variable {compE : (Γ Θ Δ : ECon) -> ESubst -> ESubst -> ESubst}
-- notation A:max"[" σ:max "]" => (substTyE . . A σ)
-- macro:max v:term noWs "[" σ:term "]" : term => `(substVarE $v $σ)
-- macro:max A:term noWs "[" σ:term "]" Γ:term:max Δ:term:max : term => `(substTyE $Γ $Δ $A $σ)
-- macro:max A:term noWs "[" σ:term "]" : term => `(fun x y => substTyE x y $A $σ)
-- macro:max t:term noWs "[" σ:term "]" : term => `(fun x y => substTmE x y $t $σ)
-- notation σ " ∘ " δ => (comp . . . σ δ)

-- ## Custom size measure `‖_‖`.
mutual
  @[aesop unsafe] def ECon.size : ECon -> Nat
  | .nil => 1
  | .ext Γ A => 1 + Γ.size + A.size

  @[aesop unsafe] def ETy.size : ETy -> Nat
  | .U Δ => 1
  | .El Δ t => 1 + t.size
  | .Pi Δ A B => 1 + A.size + B.size

  @[aesop unsafe] def EVar.size : EVar -> Nat
  | .vz .. => 0
  | .vs _ _ v => 1 + v.size

  @[aesop unsafe] def ETm.size : ETm -> Nat
  | .var _ v => 1 + v.size
  | .app _ _ _ f a => 1 + f.size + a.size
  | .lam _ _ _ body => 1 + body.size
  | .error => 0

  @[aesop unsafe] def ESubst.size : ESubst -> Nat
  | .nil .. => 1
  | .cons _ _ _ σ t => 1 + σ.size + t.size
end
notation "‖" x:60 "‖" => ECon.size x
notation "‖" x:60 "‖" => ETy.size x
notation "‖" x:60 "‖" => ETm.size x
notation "‖" x:60 "‖" => EVar.size x
notation "‖" x:60 "‖" => ESubst.size x

@[aesop unsafe] theorem ECon.get_lt_con (Γ : ECon) (n : Fin ∣Γ∣) : ‖Γ.get n‖ < ‖Γ‖ := sorry
@[aesop unsafe] theorem ECon.len_le_sizeOf (Γ : ECon) : ∣Γ∣ <= ‖Γ‖ := sorry
@[aesop unsafe] theorem ESubst.len_le_sizeOf (σ : ESubst) : ∣σ∣ <= ‖σ‖ := sorry
-- Not provable in the erased version, because type indices not constrained:
-- @[aesop unsafe] theorem ESubst.len_eq_Δ (σ : ESubst) : ∣σ∣ = ∣σ.Δ∣ := sorry
-- @[aesop unsafe] theorem ESubst.len_eq_Δ' (σ : ESubst) : σ.Δ = ΔΔ -> ∣σ∣ = ∣ΔΔ∣ := sorry
@[aesop unsafe] def ESubst_size (σ : ESubst) : ‖σ‖ = 1 + ∣σ∣ + sum 0 ∣σ∣ (fun v hv => ‖σ.get ⟨v, hv.2⟩‖) := sorry

mutual
  /-- Counts how many times variable `v` occurs in the type, ignoring type indices. -/
  def freqTy (Γ : ECon) (v : Fin ∣Γ∣) : ETy -> Nat
  | .U _ => 0
  | .El _ t => freqTm Γ v t
  | .Pi _ A B => freqTy Γ v A + freqTy (.ext Γ A) ⟨v + 1, by rw [ECon.len]; omega⟩ B
  /-- Counts how many times variable `v` occurs in the term, ignoring type indices. -/
  def freqTm (Γ : ECon) (v : Fin ∣Γ∣) : ETm -> Nat
  | .var _ var => if var.deBrujin = v then 1 else 0
  | .app _ A B f a => freqTm Γ v f + freqTm Γ v a -- ignore type indices A and B
  | .error => 99999
  | .lam .. => 99999 -- todo
end

/-- `(wkn Γ n).size`. Because `wkn (Con.nil, A, B, C) 1 ≡ (Subst.nil, Tm.var #2, Tm.var #1)`,
  so `1` for `Subst.nil`, and then for every term in the subst we have 1 for `Subst.cons`,
  1 for `Tm.var`, and `i` for de brujin `#i`. The `i` may not even be necessary actually,
  making the `sum` needless, but for now I've included `i` just in case. -/
def wkn.size (Γ : ECon) (n : Fin (Γ.len + 1)) : Nat := 1 + sum n ∣Γ∣ (fun i _ => 2 + i)
def wknSize (Γlen : Nat) (n : Fin (Γlen + 1)) : Nat := 1 + sum n Γlen (fun i _ => 2 + i)
@[aesop safe, simp] theorem wkn_size (Γ : ECon) (n : Fin (Γ.len + 1)) : ‖wknE Γ n‖ = wkn.size Γ n := sorry

/-
  ## cost functions
  These functions are the "variables" in the system of inequalities below.
-/
@[simp] noncomputable abbrev substTy? (Γ Δ : ECon) (A : ETy) (σ : ESubst) : Nat := ‖Γ‖ + ‖substTyE Γ Δ A σ‖ + ‖wknE (.ext Γ (substTyE Γ Δ A σ)) 1‖
@[simp] noncomputable abbrev substTm? (Γ Δ : ECon) (t : ETm) (σ : ESubst) : Nat := 0 -- todo
@[simp] noncomputable abbrev wkn? (Γ : ECon) (n : Fin (Γ.len + 1)) : Nat := ‖Γ‖ + ∣Γ∣ - n + ‖wknE Γ n‖
@[simp] noncomputable abbrev mkVar? (Γ : ECon) (v : Fin Γ.len) : Nat := ‖Γ‖ + ‖wknE Γ ⟨v+1, by aesop⟩‖ + v
@[simp] noncomputable abbrev comp? (Γ Θ Δ : ECon) (δ σ : ESubst) : Nat := ‖δ‖ + ‖σ‖

-- ## one theorem per recursive callsite

theorem substTy_1 (t : ETm) (σ : ESubst) : substTm? Γ Δ t σ < @substTy? substTyE wknE Γ Δ (.El Δ t) σ := sorry
theorem substTy_2 (A B : ETy) (σ : ESubst) : @substTy? substTyE wknE Γ Δ A σ < @substTy? substTyE wknE Γ Δ (.Pi Δ A B) σ := sorry
theorem substTy_3 (A B : ETy) (σ : ESubst) : @wkn? wknE (.ext Γ (substTyE Γ Δ A σ)) 1 < @substTy? substTyE wknE Γ Δ (.Pi Δ A B) σ := sorry
theorem substTy_4 (A B : ETy) (σ : ESubst) : comp? (.ext Γ (substTyE Γ Δ A σ)) Γ Δ σ (wknE (.ext Γ (substTyE Γ Δ A σ)) 1) < @substTy? substTyE wknE Γ Δ (.Pi Δ A B) σ := sorry
theorem substTy_5 (A B : ETy) (σ : ESubst) : @substTy? substTyE wknE (.ext Γ (substTyE Γ Δ A σ)) (.ext Δ A) B (compE (.ext Γ (substTyE Γ Δ A σ)) Γ Δ σ (wknE (.ext Γ (substTyE Γ Δ A σ)) 1)) < @substTy? substTyE wknE Γ Δ (.Pi Δ A B) σ := sorry

theorem substTm_1 (f a : ETm) (σ : ESubst) : substTm? Γ Δ f σ < substTm? Γ Δ (.app Δ A B f a) σ := sorry
theorem substTm_2 (f a : ETm) (σ : ESubst) : substTm? Γ Δ a σ < substTm? Γ Δ (.app Δ A B f a) σ := sorry
theorem substTm_3 (f a : ETm) (σ : ESubst) : @wkn? wknE (.ext Γ (substTyE Γ Δ A σ)) 1 < substTm? Γ Δ (.app Δ A B f a) σ := sorry
theorem substTm_4 (f a : ETm) (σ : ESubst) : comp? (.ext Γ (substTyE Γ Δ A σ)) Γ Δ σ (wknE (.ext Γ (substTyE Γ Δ A σ)) 1) < substTm? Γ Δ (.app Δ A B f a) σ := sorry
theorem substTm_5 (f a : ETm) (σ : ESubst) : @substTy? substTyE wknE (.ext Γ (substTyE Γ Δ A σ)) (.ext Δ A) B (compE (.ext Γ (substTyE Γ Δ A σ)) Γ Δ σ (wknE (.ext Γ (substTyE Γ Δ A σ)) 1)) < substTm? Γ Δ (.app Δ A B f a) σ := sorry

theorem wkn_1 (Γ : ECon) (n : Fin (Γ.len + 1)) (h : n < Γ.len) : @wkn? wknE Γ (n+1) < @wkn? wknE Γ n := by
  simp_all only [wkn?, wkn_size, wkn.size, sum_begin]
  rw [Fin.add_val_pull h]
  omega
theorem wkn_2 (Γ : ECon) (n : Fin (Γ.len + 1)) : (h : n < Γ.len) -> @mkVar? wknE Γ ⟨n, sorry⟩ < @wkn? wknE Γ n := sorry

theorem mkVar_1 (Γ : ECon) (v : Fin Γ.len) : @wkn? wknE Γ (v.castAdd 1) < @mkVar? wknE (.ext Γ X) (ECon.len.eq_2 .. ▸ v.natAdd 1) := sorry
theorem mkVar_2 (Γ : ECon) (v : Fin Γ.len) (h : v + 1 < ∣.ext Γ X∣) :
  (@substTy? substTyE wknE
    Γ
    (Γ.drop ⟨v+1, by rw [ECon.len] at h; linarith⟩)
    (Γ.get ⟨v, by rw [ECon.len] at h; linarith⟩) -- `Γᵥ`
    (wknE (.ext Γ X) ⟨v+1+1, by simp_all only [ECon.len, add_lt_add_iff_right]⟩) -- `wkn (Γ, X) (v+1+1)`
  ) -- `Γᵥ[wkn (Γ, X) (v+1+1)]`
  < @mkVar? wknE (.ext Γ X) (ECon.len.eq_2 .. ▸ v.natAdd 1)
  := sorry
theorem mkVar_3 (Γ : ECon) (v : Fin Γ.len)       : @mkVar? wknE Γ v < @mkVar? wknE (.ext Γ X) (ECon.len.eq_2 .. ▸ v.natAdd 1) := sorry

-- not 100% on the rhs of `<` of these two:
theorem comp_1 (δ σ : ESubst) : comp? Γ Θ Δ δ σ < comp? Γ Θ (.ext Δ A) (.cons Θ Δ A δ t) σ := by sorry
theorem comp_2 (δ σ : ESubst) : substTm? Γ Θ t σ < comp? Γ Θ (.ext Δ A) (.cons Θ Δ A δ t) σ := sorry
end DecreasingMeasure

#check Fin.castSucc
#check Fin.val_add_one_of_lt

/-- If `n` is not the last element, we can add one without wrapping around. -/
abbrev Fin.addOne (n : Fin (N+1)) (h : n.val < N) : Fin (N+1) := ⟨n.val + 1, by omega⟩

mutual
  /-- `wkn {Γ : Con} (n : Fin (Γ.len + 1)) : (Γ <- Γ - n)` -/
  def wknE (Γ : ECon) (n : Fin (Γ.len + 1)) : ESubst :=
    if h : Γ.len = n then .nil Γ
    else
      have h : n < ∣Γ∣ := by omega
      ESubst.cons
        Γ
        (Γ.drop (n.addOne h))
        (Γ.get ⟨n.val, h⟩) -- Γₙ
        (wknE Γ (n.addOne h)) -- `wkn Γ (n+1) : Γ <- Γ - (n+1)`
        (.var Γ
          -- (substTyE Γ (Γ.drop (n+1)) (Γ.get ⟨n, by simp only [h]⟩) (wkn Γ ⟨n+1, by linarith⟩)) -- `Γᵥ[wki]`
          (mkVarE Γ ⟨n.val, h⟩)
        )
  termination_by Γ.len - n

  -- `mkVar : (Γ : Con) -> (v : Fin Γ.len) -> Var Γ (Γ.get v)[wkn Γ (v+1)]`
  def mkVarE : (Γ : ECon) -> (v : Fin Γ.len) -> EVar
  | .nil, v => Fin.elim0 v
  | .ext Γ X, ⟨0  , _⟩ => -- expected `Var (Γ, X) (get (Γ, X) 0)[wkn (Γ, X) (0 + 1)]`
    -- by defeq we have `get (Γ, X) 0 ≡ X`
    .vz Γ X -- `: Var (Γ, X) X[wki]`, where `wki` is just a shorthand for `wkn (Γ, X) 1`.
  | .ext Γ X, ⟨v+1, h⟩ => -- expected `Var (Γ, X) (get (Γ, X) (v+1))[wkn (Γ, X) (v + 1 + 1)]`
    -- ! need theorem get_ext : get (Γ, X) (v+1) = get Γ v
    -- ! need theorem : wkn Γ (v+1) ∘ wkn (Γ, X) 1 = wkn (Γ, X) (v+1+1)
    .vs
      Γ
      -- (substTyE
      --   Γ
      --   (Γ.drop ⟨v+1, by rw [ECon.len] at h; linarith⟩)
      --   (Γ.get ⟨v, by rw [ECon.len] at h; linarith⟩) -- `Γᵥ`
      --   (wkn (.ext Γ X) ⟨v+1+1, by simp_all only [ECon.len, add_lt_add_iff_right]⟩) -- `wkn (Γ, X) (v+1+1)`
      -- ) -- `Γᵥ[wkn (Γ, X) (v+1+1)]`
      X
      (mkVarE Γ ⟨v, by rw [ECon.len] at h; linarith⟩) -- `mkVar Γ v : Var Γ (Γ.get v)[wkn Γ (v+1)]`
  termination_by Γ v => sizeOf Γ
end

#print axioms wknE

/-- Identity substitution. `id : {Γ : Con} -> (Γ <- Γ)`. Just a shorthand for `wkn Γ 0`. -/
def idE (Γ : ECon) : ESubst := wknE Γ 0

/-- Weakened identity substitution. `wki : {Γ : Con} -> {W : Ty Γ} -> (Γ, W <- Γ)`. Just a shorthand for `wkn (Γ, W) 1`. -/
def wkiE (Γ : ECon) (W : ETy) : ESubst := wknE (.ext Γ W) 1

mutual
  /-- `substTy {Γ Δ : Con} (A : Ty Δ) (σ : Γ <- Δ) : Ty Γ` -/
  unsafe def substTyE (Γ Δ : ECon) : ETy -> ESubst -> ETy
  | .U Δ, σ => .U Γ
  | .El Δ t, σ => .El Γ (substTmE Γ Δ t σ)
  | .Pi Δ A B, σ => -- Δ ⊢ A
    let Aσ : ETy /- Γ -/ := substTyE Γ Δ A σ -- `Γ ⊢ A[σ]`
    let wk_σ /- : (Γ, A[σ]) <- Δ -/ := compE (.ext Γ Aσ) Γ Δ σ (wknE (.ext Γ Aσ) 1) -- note that `wk σ = σ ∘ (wkn (Γ, A[σ]) 1)`
    -- let A_wk_σ : ETy := substTyE (.ext Γ Aσ) Δ A wk_σ -- `(Γ, A[σ]) ⊢ A[wk σ]`
    let vz : ETm /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ Aσ) (.vz Γ Aσ) -- `.vz Γ A' : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = σ ∘ (wk id)`
    let δ : ESubst /- (Γ, A[σ]) <- (Δ, A) -/ := .cons (.ext Γ Aσ) Δ A (wk_σ) vz
    .Pi Γ Aσ (substTyE (.ext Γ Aσ) (.ext Δ A) B δ)
  termination_by A σ => sizeOf A + sizeOf σ

  /-- `substTm {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ (substTy A σ)` -/
  unsafe def substTmE (Γ Δ : ECon) : ETm -> ESubst -> ETm
  | .var _ v, σ => substVarE v σ -- just pick the term in the subst that v refers to. if ill-formed, then .error.
  | .app _Δ A B f a, σ => -- `Δ ⊢ a : A`, `Δ ⊢ f : Pi A B`, expected `Tm Γ B[id, a][σ]`    (yes this `A` is the same as the `A` in `@substTm _ _ A ..`)
    let Aσ : ETy /- Γ -/ := substTyE Γ Δ A σ -- Γ ⊢ A[σ]
    -- let wk_σ : ESubst := wkE Γ Δ A' σ -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wk id)`
    let wk_σ : ESubst := compE (.ext Γ Aσ) Γ Δ σ (wknE (.ext Γ Aσ) 1) -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wkn (Γ, A[σ]) 1)`
    -- let A_wk_σ : ETy /- (Γ, A[σ]) -/ := substTyE (.ext Γ Aσ) Δ A wk_σ -- A[wk σ]
    let vz : ETm /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ Aσ) (.vz Γ Aσ) -- `.vz Γ A[σ] : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = (wk id) ∘ σ`
    let δ : ESubst /- (Γ, A[σ]) <- (Δ, A) -/ := ESubst.cons (.ext Γ Aσ) Δ A (wk_σ) vz

    let B' : ETy := substTyE (.ext Γ Aσ) (.ext Δ A) B δ
    let f' : ETm := substTmE Γ Δ f σ -- `f[σ] : Tm Γ (Pi A B)[σ]`, where `(Pi A B)[σ] = Pi A[σ] B[wk σ, #0]` per definition of substTy
    let a' : ETm := substTmE Γ Δ a σ -- `a[σ] : Tm Γ A[σ]`
    let fa' : ETm := .app Γ Aσ B' f' a' -- `.app f[σ] a[σ] : Tm Γ B[wk σ, #0][id, a]`
    fa' -- ! here we need `((wk σ), #0) ∘ (id, a) = (id, a) ∘ σ` to typecheck.
  | .lam Δ A B body, σ => .error
  | .error, _ => .error
  termination_by t σ => sizeOf t + sizeOf σ

  /-- `comp {Γ Θ Δ : Con} : Subst Θ Δ -> Subst Γ Θ -> Subst Γ Δ` -/
  unsafe def compE (Γ Θ Δ : ECon) : ESubst -> ESubst -> ESubst
  | .nil Θ         , σ => .nil Γ
  | .cons Θ Δ A δ t, σ => -- `δ : Θ <- Δ`,   `σ : Γ <- Θ`,   `Θ ⊢ t : A[δ]`,   expected `Γ <- Δ, A`
    .cons Γ Δ A
      (compE Γ Θ Δ δ σ) -- δ ∘ σ : Γ <- Δ
      (substTmE Γ Θ t σ) -- `Γ ⊢ t[σ] : A[δ][σ]`, -- ! need theorem `A[δ][σ] = A[δ ∘ σ]`
  termination_by δ σ => sizeOf δ + sizeOf σ
end

/-- `wk : {Γ Δ : Con} -> {W : Ty Γ} -> (Γ <- Δ) -> (Γ, W <- Δ)` -/
unsafe def wkE (Γ Δ : ECon) (W : ETy) (σ : ESubst) : ESubst
  := compE (.ext Γ W) Γ Δ σ (wkiE Γ W) -- `wki : Γ,W <- Γ`

/-- Parellel weakening `wkp {Γ Δ} {A : Ty Δ} (σ : Γ <- Δ) : (Γ, A[σ]) <- (Δ, A)`. This is the `δ` used in substTyE and substTmE. -/
unsafe def wkpE (Γ Δ : ECon) (A : ETy) (σ : ESubst) : ESubst :=
  let Aσ : ETy /- Γ -/ := substTyE Γ Δ A σ -- `Γ ⊢ A[σ]`
  let wk_σ : ESubst := compE (.ext Γ Aσ) Γ Δ σ (wknE (.ext Γ Aσ) 1) -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wkn (Γ, A[σ]) 1)`
  let vz : ETm /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ Aσ) (.vz Γ Aσ) -- `.vz Γ A[σ] : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = (wk id) ∘ σ`
  let δ : ESubst /- (Γ, A[σ]) <- (Δ, A) -/ := ESubst.cons (.ext Γ Aσ) Δ A wk_σ vz
  .cons (.ext Γ Aσ) Δ A wk_σ vz

section Tests
  def F'' : ETy := .Pi (.nil) (.U .nil) (.U .nil)
  -- def Γ : ECon := (.ext (.ext (.ext .nil (.U .nil)) F) F)
  def Γe'' : ECon := .ext (.ext (.ext (.ext .nil (.U .nil)) F'') F'') F''
  #reduce sizeOf <| idE Γe''
  #reduce sizeOf <| wkpE Γe'' Γe'' F'' <| idE Γe''

  #eval idE .nil
  #reduce sizeOf (idE .nil)
  #reduce sizeOf (idE (.ext .nil (.U .nil)))

  #eval idE (.ext .nil (.U .nil))
  #eval idE (.ext (.ext .nil (.U .nil)) (.U .nil))
  #eval idE (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

  def wk1 (Γ : ECon) : ESubst := wknE Γ 1
  #eval wk1 (.ext .nil (.U .nil))
  #eval wk1 (.ext (.ext .nil (.U .nil)) (.U .nil))
  #eval wk1 (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

  def wk2 (Γ : ECon) : ESubst := wknE Γ 2
  #eval wk2 (.ext (.ext .nil (.U .nil)) (.U .nil))
  #eval wk2 (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

  -- #eval wkpE Γe Γe (.U Γe) <| idE Γe
end Tests


/-- `def idxA : Var Γ A -> Ty Γ := A`. Reconstruct the `A` in `Var Γ A`. -/
noncomputable unsafe def EVar.idxA : EVar -> ETy
| .vz Γ A => A
| .vs Γ B v => -- `.vs v : Var (Γ, B) A[wkn (Γ, B) 1]`, and `v : Var A Γ`, and ~~`Γ⊢A`~~, and `Γ,A⊢B`, expecting `Ty (Γ, B)`.
  let A := v.idxA -- `Γ ⊢ A`
  -- let A_wk := A[wkn (.ext Γ B) 1] Γ (.ext Γ B)  -- `Γ, B ⊢ A[wkn (Γ, B) 1]`
  let A_wk := substTyE Γ (.ext Γ B) A (wknE (.ext Γ B) 1) -- `Γ, B ⊢ A[wkn (Γ, B) 1]`
  A_wk

-- /-- Reconstruct the `A` in `Tm Γ A`. -/
-- noncomputable unsafe def ETm.idxA : ETm -> ETy
-- | .var Γ v => v.idxA
-- | .app Γ A B f a => A -- this is the one spot where we *need* to store `A`. Intuitively, `.app` is modus ponens, so similar to cuts in sequent calculus. We can't do cut elimination in Lean afaik, so we are unable to reconstruct `A` here.
-- | .lam .. => sorry
-- | .error .. => sorry

mutual
  @[aesop safe constructors unsafe cases]
  unsafe inductive ConW : ECon -> Prop
  | nil : ConW .nil
  | ext : (Γw : ConW Γ) -> (Aw : TyW Γ A) -> ConW (.ext Γ A)

  @[aesop safe constructors unsafe cases]
  unsafe inductive TyW : ECon -> ETy -> Prop
  | U : ConW Γ -> TyW Γ (.U Γ)
  | El : ConW Γ -> TmW Γ (.U Γ) t -> TyW Γ (.El Γ t)
  | Pi : ConW Γ -> TyW Γ A -> TyW (.ext Γ A) B -> TyW Γ (.Pi Γ A B)
  /-- A mutual inductive type which may refer to existing types in Γ, and has type A. -/
  -- | mind : MInd /- Γ -/ A -> Ty Γ

  @[aesop safe constructors unsafe cases]
  unsafe inductive VarW : ECon -> ETy -> EVar -> Prop
  /-`vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]` -/
  | vz : ConW Γ -> TyW Γ A -> VarW (.ext Γ A) (substTyE (.ext Γ A) Γ A (wkiE Γ A)) (.vz Γ A)
  /- `vs {Γ} ~~{A : Ty Γ}~~ {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]` -/
  | vs : ConW Γ -> TyW Γ A -> TyW Γ B -> VarW Γ A v
    -> VarW (.ext Γ B) (substTyE (.ext Γ B) Γ A (wkiE Γ B)) (.vs Γ /- ~~A~~ -/ B v)

  @[aesop safe constructors unsafe cases]
  unsafe inductive TmW : ECon -> ETy -> ETm -> Prop
  /- var {Γ} ~~{A : Ty Γ}~~ : Var Γ A -> Tm Γ A -/
  | var : ConW Γ -> /- ~~ TyW Γ A -> ~~-/ VarW Γ A v -> TmW Γ A (.var Γ /- ~~A~~ -/ v)
  /- `app {Γ : Con} {A : Ty Γ} {B : Ty (Γ, A)} : (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[id, a]`
    Here, `(id Γ, a)` is `Γ <- Γ, A`. -/
  | app : ConW Γ -> TyW Γ A -> TyW (.ext Γ A) B ->
    TmW Γ (.Pi Γ A B) f ->
    TmW Γ A a ->
    TmW Γ (substTyE Γ (.ext Γ A) B (.cons Γ (.ext Γ A) A (idE Γ) a)) (.app Γ A B f a)
  -- | lam : {Aw : TyW Γe Ae} ->
  --         {Bw : TyW (.ext Γe Ae) Be} ->
  --         (bodyw : TmW (.ext Γe Ae) Be bodye) ->
  --         TmW Γe (.Pi Ae Be) (.lam bodye)

  @[aesop safe constructors unsafe cases]
  unsafe inductive SubstW : ECon -> ECon -> ESubst -> Prop
  | nil : ConW Γ -> SubstW Γ .nil (.nil Γ)
  /- Subst.cons {Γ} {Δ} {A : Ty Δ} : (δ : Γ <- Δ) -> (t : Tm Γ A[δ]) -> (Γ <- (Δ, A)) -/
  | cons : ConW Γ -> ConW Δ -> TyW Δ A ->
      SubstW Γ Δ δ ->
      TmW Γ (substTyE Γ Δ A δ) t ->
      SubstW Γ (.ext Δ A) (.cons Γ Δ A δ t)
end

@[simp] theorem Γ_len0_nil {Γ : ECon} {n : Fin (Γ.len + 1)} (h : Γ.len = 0) : Γ = .nil :=
  match Γ with
  | .nil => rfl
  | .ext Γ A => by rw [ECon.len] at h; rename_i Γ_1; simp_all only [add_eq_zero, one_ne_zero, false_and]

@[simp] theorem drop_0' : {Γ : ECon} -> {h : 0 < ∣Γ∣ + 1} -> Γ ─ ⟨0, h⟩ = Γ
| .nil    , _ => rfl
| .ext Γ A, h => ECon.drop.eq_2 Γ A h

@[simp] theorem drop_0 : {Γ : ECon} -> Γ ─ 0 = Γ := drop_0'

@[simp] theorem drop_ext_1' : {Γ : ECon} -> {h : 1 < ∣Γ.ext A∣ + 1} -> .ext Γ A ─ ⟨1, h⟩ = Γ
| .nil    , _ => by simp only [ECon.drop, Fin.zero_eta, Fin.isValue, drop_0]
| .ext Γ A, h => by simp only [ECon.drop, Fin.zero_eta, drop_0]
-- @[simp] theorem drop_ext_1 : {Γ : ECon} -> .ext Γ A ─ 1 = Γ := by aesop

@[simp] theorem drop_all {Γ : ECon} {n : Fin (Γ.len + 1)} (h : Γ.len = n) : Γ ─ n = .nil :=
  match Γ, n with
  | Γ, 0 => by
    rw [Γ_len0_nil h, drop_0]
    exact 0 -- this is so weird?
  | .ext Γ A, ⟨.succ n, hsn⟩ => by
    rw [ECon.drop]
    exact @drop_all Γ ⟨n, by simp_all only [ECon.len, Nat.succ_eq_add_one]; rw [add_comm, h]; simp⟩
      (by -- ugly proof
        simp_all only
        simp_all only [Nat.succ_eq_add_one, lt_add_iff_pos_right, zero_lt_one]
        rw [ECon.len.eq_2] at h
        omega)

@[simp] theorem wknE_all {Γ : ECon} {n : Fin (Γ.len + 1)} (h : Γ.len = n) : wknE Γ n = .nil Γ := by
  rw [wknE]
  simp only [dite_eq_left_iff, imp_false, Decidable.not_not]
  exact h

@[aesop safe] unsafe def dropW : (Γw : ConW Γ) -> (n : Fin (∣Γ∣+1)) -> ConW (Γ ─ n)
| ConW.nil    , n => .nil
| Γw, ⟨0  , h⟩ => by rw [drop_0']; exact Γw
| @ConW.ext Γ A Γw Aw, ⟨n+1, h⟩ => by
  rw [ECon.drop]
  exact dropW Γw ⟨n, by rw [ECon.len] at h; omega⟩

@[aesop safe] unsafe def getW {Γ : ECon} : (Γw : ConW Γ) -> (v : Fin Γ.len) -> TyW (Γ ─ v.succ) (Γ.get v)
| .nil    , v => Fin.elim0 v
| @ConW.ext Γ A Γw Aw, ⟨0  , h⟩ => by simp only [Fin.succ_mk, Nat.succ_eq_add_one, zero_add, ECon.drop, drop_0', ECon.get]; exact Aw
| @ConW.ext Γ A Γw Aw, ⟨v+1, h⟩ => by simp [ECon.drop, ECon.get]; exact getW Γw ⟨v, by rw [ECon.len] at h; omega⟩

/-- `(Γ - (v+1), Γᵥ) = Γ - v` -/
@[simp]
theorem con_ext_get' (Γ : ECon) (v : Fin Γ.len) (h1 : ↑v + 1 < ∣Γ∣ + 1) (h2 : ↑v < ∣Γ∣) (h' : ↑v < ∣Γ∣ + 1)
  : .ext (Γ ─ ⟨v+1, h1⟩) (Γ.get ⟨v, h2⟩) = Γ ─ ⟨v, h'⟩
  := by
  match Γ, v with
  | .nil    , n => exact Fin.elim0 n
  | .ext Γ A, ⟨0  , h⟩ => simp only [zero_add, drop_ext_1', ECon.get, Fin.zero_eta, drop_0]
  | .ext Γ A, ⟨v+1, h⟩ =>
    have ih := con_ext_get' Γ ⟨v, by rw [ECon.len] at h; omega⟩ (by omega) (by omega) (by omega)
    simp only [ECon.drop, ECon.get, ih]

-- theorem con_ext_get (Γ : ECon) (v : Fin Γ.len) : .ext (Γ ─ v.succ) (Γ.get v) = Γ ─ v.castSucc := by sorry -- con_ext_get'

mutual
  /-- `wkn {Γ : Con} (n : Fin (Γ.len + 1)) : (Γ <- Γ - n)` -/
  unsafe def wknW (Γw : ConW Γ) (n : Fin (Γ.len + 1)) : SubstW Γ (Γ ─ n) (wknE Γ n) := by
    -- SubstW.nil {Γe : ECon} : ConW Γe → SubstW ECon.nil Γe (ESubst.nil Γe)
    if h : Γ.len = n then
      rw [wknE_all h, drop_all h]
      exact @SubstW.nil Γ Γw
    else
      have h : n.val < ∣Γ∣ := by omega
      -- reminder: `Subst.cons {Γ} {Δ} {A : Ty Δ} : (δ : Γ <- Δ) -> (t : Tm Γ A[δ]) -> (Γ <- (Δ, A))`
      have := SubstW.cons
        Γw  -- Γ := Γ
        (dropW Γw (n.addOne h)) -- Δ := Γ ─ (n+1)
        (getW Γw ⟨n.val, h⟩) -- A := Γₙ
        -- `Subst.cons Γ (Γ ─ (n+1)) Γₙ : (δ : Γ <- (Γ ─ (n+1))) -> (t : Tm Γ Γₙ[δ]) -> (Γ <- (Γ ─ (n+1), Γₙ))`
        (wknW Γw (n.addOne h))
        -- `Subst.cons Γ (Γ ─ (n+1)) Γₙ (wkn Γ (n+1)) : (t : Tm Γ Γₙ[wkn Γ (n+1)]) -> (Γ <- (Γ ─ (n+1), Γₙ))`
        (.var
          Γw
          (mkVarW Γw ⟨n.val, h⟩)
        )
      simp [ECon.drop, Fin.addOne] at this
      let v : Fin Γ.len := ⟨n, by omega⟩ -- maybe adapting `con_ext_get'` makes more sense than introducing this v
      have rw := con_ext_get' Γ v (by omega) (by omega) (by omega)
      -- have n_is_v : n.val = v.val := by simp_all only [Fin.eta]
      -- rw [n_is_v] at h
      rw [rw] at this
      clear rw
      rw [wknE]
      simp [reduceDite] -- why doesn't it simp away the `if` :(
      -- this almost works, just a bit of fiddling around with Fin
      exact this

  -- `mkVar : (Γ : Con) -> (v : Fin Γ.len) -> Var Γ Γₙ[wkn Γ (v+1)]`
  unsafe def mkVarW : (Γw : ConW Γ) -> (v : Fin Γ.len) ->
    VarW Γ (substTyE Γ (Γ ─ ⟨v.val + 1, by omega⟩) (Γ.get ⟨v.val, by omega⟩) (wknE Γ v.succ)) (mkVarE Γ v)
  | .nil, v => Fin.elim0 v
  | @ConW.ext Γe Xe Γw Xw, ⟨0  , h⟩ => by -- expected `Var (Γ, X) (get (Γ, X) 0)[wkn (Γ, X) (0 + 1)]`
    -- by defeq we have `get (Γ, X) 0 ≡ X`
    rw [wknE]
    rw [mkVarE]
    simp

    exact .vz Γw Xw -- `: Var (Γ, X) X[wki]`, where `wki` is just a shorthand for `wkn (Γ, X) 1`.
  | .ext Γ X, ⟨v+1, h⟩ => -- expected `Var (Γ, X) (get (Γ, X) (v+1))[wkn (Γ, X) (v + 1 + 1)]`
    -- ! need theorem get_ext : get (Γ, X) (v+1) = get Γ v
    -- ! need theorem : wkn Γ (v+1) ∘ wkn (Γ, X) 1 = wkn (Γ, X) (v+1+1)
    .vs
      Γ
      -- (substTyE
      --   Γ
      --   (Γ.drop ⟨v+1, by rw [ECon.len] at h; linarith⟩)
      --   (Γ.get ⟨v, by rw [ECon.len] at h; linarith⟩) -- `Γᵥ`
      --   (wkn (.ext Γ X) ⟨v+1+1, by simp_all only [ECon.len, add_lt_add_iff_right]⟩) -- `wkn (Γ, X) (v+1+1)`
      -- ) -- `Γᵥ[wkn (Γ, X) (v+1+1)]`
      X
      (mkVarE Γ ⟨v, by rw [ECon.len] at h; linarith⟩) -- `mkVar Γ v : Var Γ (Γ.get v)[wkn Γ (v+1)]`
  -- termination_by Γ v => sizeOf Γ
end



-- # !
-- # Everything below this line is VERY out of date!

#exit

#check WTm.app
#check ESubst.vshift
/-- `Tm Γ A -> Tm (Γ, B) A` -/
theorem WSubst.vshift (Γw : WCon Γe) (Aw : WTy Γe Ae) (Bw : WTy (.ext Γe Ae) Be) (tw : WTm Γe Ae te)
  : WTm (.ext Γe Be) Ae (ESubst.vshift te)
  := sorry
    -- match h : te, tw with
    -- | .var ve, .var vw => by
    --   rw [ESubst.vshift]
    --   exact .var (.vs vw)
    -- | @ETm.app fe ae, @WTm.app Γe .(fe) .(ae) Ae Be Aw' Bw' fw aw => by -- ESubst.vshift (.app f a) ≡ .app (vshift f) (vshift a)
    --   rw [ESubst.vshift]
    --   let ih_f := vshift
    --   -- aesop
    --   -- have h1 := sorry
    --   exact @WTm.app (.ext Γe Be) _ _ _ _ _ _ sorry sorry
    --   done
    -- | .lam body, .lam bodyw => sorry -- .lam (vshift body)
    -- | .error, h => sorry

/-- `Subst Γ Δ -> Subst (Γ, A) Δ` -/
def WSubst.weaken (Γw : WCon Γe) (Δw : WCon Δe) (Aw : WTy Γe Ae) : (σw : WSubst Γe Δe σe) -> WSubst (.ext Γe Ae) Δe (weakenE σe) := sorry

/-- `Subst Γ Γ` -/
def WSubst.id (Γw : WCon Γe) : WSubst Γe Γe (ESubst.id Γe) := sorry

/-- `Subst (Γ, A) Γ`. This is usually two functions chained together: `wk id`, but we only need this version. -/
def WSubst.wk (Γw : WCon Γe) (Aw : WTy Γe Ae) : WSubst (.ext Γe Ae) Γe (ESubst.wk Γe) := sorry

/-- `subst1 : Subst Γ (Γ, A) -/
def WSubst.subst1 (Γw : WCon Γe) (Aw : WTy Γe Ae) : WSubst Γe (.ext Γe Ae) (ESubst.id Γe) := sorry

-- theorem substVarW : (vE : EVar) -> (σE : ESubst) -> (tE : ETm) -> W

/-- Remember that `def substTy {Γ Δ : Con} : Ty Δ -> Subst Γ Δ -> Ty Γ` -/
theorem substTyW {Γe Δe : ECon} {Ae : ETy} (Aw : WTy Δe Ae) {σe : ESubst} (σw : WSubst Γe Δe σe)
  : WTy Γe (substTyE Ae σe) := sorry

theorem substTmW {Γe Δe : ECon} {te : ETm} (tw : WTm Δe Ae te) {σe : ESubst} (σw : WSubst Γe Δe σe)
  : WTm Γe (substTyE Ae σe) (substTmE te σe) := sorry

theorem wkW (Γw : WCon Γe) (Aw : WTy Γe Ae) : WSubst (.ext Γe Ae) Γe (ESubst.wk Γe) := sorry

theorem subst1W (Γw : WCon Γe) (Aw : WTy Γe Ae) (tw : WTm Γe Ae te) : WSubst Γe (ECon.ext Γe Ae) (ESubst.subst1 Γe te) := sorry -- maybe? very wild guess

section Hooray
  def Con : Type _ := @PSigma ECon WCon
  def Ty (Γ : Con) : Type _ := @PSigma ETy (WTy Γ.fst)
  def Var (Γ : Con) (A : Ty Γ) : Type _ := @PSigma EVar (WVar Γ.fst A.fst)
  def Tm (Γ : Con) (A : Ty Γ) : Type _ := @PSigma ETm (WTm Γ.fst A.fst)
  def Subst (Γ : Con) (Δ : Con) : Type _ := @PSigma ESubst (WSubst Γ.fst Δ.fst)

  def Con.nil : Con := ⟨.nil, .nil⟩
  def Con.ext (Γ : Con) (A : Ty Γ) : Con := ⟨.ext Γ.fst A.fst, .ext Γ.snd A.snd⟩

  def wk : Subst (Con.ext Γ A) Γ := ⟨ESubst.wk Γ.fst, wkW Γ.snd A.snd⟩
  def substTy {Γ Δ : Con} (A : Ty Δ) (σ : Subst Γ Δ) : Ty Γ := ⟨substTyE A.fst σ.fst, substTyW A.snd σ.snd⟩
  def substTm {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ (substTy A σ) := ⟨substTmE t.fst σ.fst, substTmW t.snd σ.snd⟩

  def Ty.U : Ty Γ := ⟨.U, .U⟩
  def Ty.El (t : Tm Γ U) : Ty Γ := ⟨.El t.fst, .El t.snd⟩
  def Ty.Pi (A : Ty Γ) (B : Ty (Con.ext Γ A)) : Ty Γ := ⟨.Pi A.fst B.fst, .Pi A.snd B.snd⟩
  def Var.vz : Var (Con.ext Γ A) (substTy A wk) := ⟨.vz, .vz⟩
  def Var.vs (v : Var Γ A) : Var (Con.ext Γ B) (substTy A wk) := ⟨.vs v.fst, .vs v.snd⟩

  def Subst.nil : Subst Γ Con.nil := ⟨.nil, .nil⟩
  def Subst.cons (δ : Subst Γ Δ) (t : Tm Γ (substTy A δ)) : Subst Γ (Con.ext Δ A) := ⟨.cons δ.fst t.fst, .cons δ.snd t.snd⟩

  def subst1 (t : Tm Γ A) : Subst Γ (Con.ext Γ A) := ⟨ESubst.subst1 Γ.fst t.fst, subst1W Γ.snd A.snd t.snd⟩

  def Tm.app {A : Ty Γ} {B : Ty (Con.ext Γ A)} (f : Tm Γ (Ty.Pi A B)) (a : Tm Γ A) : Tm Γ (substTy B (subst1 a)) -- Tm Γ B[Var.vz ↦ a]
    := ⟨.app f.fst a.fst, @WTm.app _ _ _ _ _ A.snd B.snd f.snd a.snd⟩
  -- def Tm.lam
  -- def Tm.var
end Hooray

def weaken : Subst Γ Δ -> Subst (.ext Γ A) Δ := sorry

/-
  def vshiftE (Γ : ECon) (A X : ETy) : ETm -> ETm
  | .var Γ A v => -- `v : Var Γ A`   ⊢   `Tm (Γ, X) (substTy A wk)`
    .var (.ext Γ X)
      -- `.var (Γ, X) : (A : Ty (Γ, X)) -> Var (Γ, X) A -> Tm (Γ, X) A`
      (substTyE A (weakenE Γ Γ X (idE Γ))) -- `weaken Subst.id : Subst (Γ, X) Γ`    `substTyE A wk : Ty (Γ, X)`
      -- `.var (Γ, X) (substTy A wk) : Var (Γ, X) (substTy A wk) -> Tm (Γ, X) (substTy A wk)`
      (.vs Γ A X -- `.vs Γ A X : Var Γ A -> Var (Γ, X) (substTy A wk)`
        v
      )
  -- Reminder: `Tm.app {Γ} : {A : Ty Γ} -> {B : Ty (Γ, A)} -> (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[Var.vz ↦ a]`
-- ! | .app Γ A B f a => -- Have   `A : Ty Γ`    `B : Ty (Γ, A)`   `f : Tm Γ (Pi A B)`    `a : Tm Γ A`      expecting `Tm (Γ, X) B[a][wk]`       note that `B[a] : Ty Γ`, and then `B[a][wk] : Ty (Γ, X)`
    .app (.ext Γ X) -- `app (Γ, X) : (A : Ty (Γ, X)) -> {B : Ty (Γ, X, A)} -> (f : Tm (Γ, X) (Pi A B)) -> (a : Tm (Γ, X) A) -> Tm (Γ, X) B[Var.vz ↦ a]`
      (substTyE A (weakenE Γ Γ X (idE Γ)))
      -- `app (Γ, X) A[wk] : {B : Ty (Γ, X, A[wk])} -> (f : Tm (Γ, X) (Pi A[wk] B)) -> (a : Tm (Γ, X) A[wk]) -> Tm (Γ, X) B[Var.vz ↦ a]`

    --   (vshiftE Γ (.Pi Γ A B) B f) -- f : Tm Γ (Pi _ _)
    --   (vshiftE Γ A B a) -- a : Tm Γ A
  | .lam Γ A B body =>
    .lam (.ext Γ B) A B (vshiftE body)
  | .error => .error

-/
#check vshiftE
def vshift {Γ : Con} {A X : Ty Γ} : Tm Γ A -> Tm (.ext Γ X) (substTy A wk)
| ⟨.var .., w⟩ => by
  have v : Var Γ A := sorry
  have goal : Tm (.ext Γ X) (substTy A wk) := sorry -- Tm.var
  sorry
| ⟨.app .., w⟩ =>
  have B : Ty (.ext Γ A) := sorry -- from pattern matching
  have f : Tm Γ (.Pi A B) := sorry -- from pattern matching
  have a : Tm Γ A := sorry -- from pattern matching
  -- unify Γ with `Γ` (because of pattern matching)
  -- unify A with `B[a]` (because of pattern matching)

  let a' : Tm (.ext Γ X) (substTy A wk) := vshift a
  let f' : Tm (.ext Γ X) (.Pi (substTy A wk) B) := sorry

  have goal : Tm (.ext Γ X) (substTy (substTy B (subst1 a)) wk) := by -- expected `Tm (Γ, X) B[a][wk]`, note that `B[a] : Ty Γ`, and then `B[a][wk] : Ty (Γ, X)`
    have asdf := @Tm.app (.ext Γ X) (substTy A wk)

    done
  sorry
| ⟨.lam .., w⟩ => sorry
| ⟨.error, _⟩ => sorry

-- def


#exit

-- # And now... the eliminator

universe u
variable {ConM : Con -> Sort u}
variable {TyM : {Γ : Con} -> (ΓM : ConM Γ) -> Ty Γ -> Sort u}
variable {VarM : {Γ : Con} -> (ΓM : ConM Γ) -> {A : Ty Γ} -> (AM : TyM ΓM A) -> Var Γ A -> Sort u}
variable {TmM :  {Γ : Con} -> (ΓM : ConM Γ) -> {A : Ty Γ} -> (AM : TyM ΓM A) -> Tm Γ A  -> Sort u}
variable {SubstM : {Γ : Con} -> (ΓM : ConM Γ) -> {Δ : Con} -> (ΔM : ConM Δ) -> Subst Γ Δ -> Sort u}
variable (nilM : ConM .nil)
variable (extM : {Γ : Con} -> (ΓM : ConM Γ) -> {A : Ty Γ} -> TyM ΓM A -> ConM (.ext Γ A))
variable (UM : {Γ : Con} -> (ΓM : ConM Γ) -> TyM ΓM .U)
variable (ElM : {Γ : Con} -> (ΓM : ConM Γ) -> (t : Tm Γ .U) -> TmM ΓM (UM ΓM) t -> TyM ΓM (.El t))
variable (PiM : {Γ : Con} -> (ΓM : ConM Γ) ->
  {A : Ty Γ}          -> (AM : TyM ΓM A) ->
  {B : Ty (.ext Γ A)} -> (BM : TyM (extM ΓM AM) B) ->
  TyM ΓM (.Pi A B))
/- ? Maybe we can always obtain substTyM, and don't need it to be a case for the recursors? -/
variable (substTyM : {Γ : Con} -> (ΓM : ConM Γ) -> {Δ : Con} -> (ΔM : ConM Δ) -> {A : Ty Δ} -> (AM : TyM ΔM A) -> (σ : Subst Γ Δ) -> TyM ΓM (substTy A σ))
variable (substNilM : {Γ : Con} -> (ΓM : ConM Γ) -> SubstM ΓM nilM .nil)
variable (substConsM : {Γ : Con} -> (ΓM : ConM Γ) -> {Δ : Con} -> (ΔM : ConM Δ) ->
  {σ : Subst Γ Δ} -> (σM : SubstM ΓM ΔM σ) ->
  (A : Ty Δ) -> (AM : TyM ΔM A) ->
  (t : Tm Γ (substTy A σ)) -> (tM : @TmM Γ ΓM (substTy A σ) (substTyM ΓM ΔM AM σ) t) ->
  SubstM ΓM (extM ΔM AM) (.cons σ t))
variable (appM : {Γ : Con} -> (ΓM : ConM Γ) ->
  (A : Ty Γ) ->           (AM : TyM ΓM           A) ->
  (B : Ty (.ext Γ A)) ->  (BM : TyM (extM ΓM AM) B) ->
  (f : Tm Γ (.Pi A B)) -> (fM : TmM ΓM (PiM ΓM AM BM) f) ->
  (a : Tm Γ A) ->         (aM : TmM ΓM AM a) ->
  TmM ΓM (substTyM ΓM (extM ΓM AM) BM (subst1 a)) (.app f a))

set_option pp.proofs.threshold 5
mutual
  def Tm.rec' {ΓM : ConM Γ} {AM : TyM ΓM A} : (te : ETm) -> (tw : WTm Γ.fst A.fst te) -> TmM ΓM AM ⟨te, tw⟩
  | .var v, w => sorry
  | .app fe ae, w => by
    rename Ty Γ => B_subst_a -- `B_subst_a ≡ B[Var.vz ↦ a]`
    -- `f        : Tm Γ (Pi A B)`
    -- `a        : Tm Γ A`
    -- `.app f a : Tm Γ B[Var.vz ↦ a]`
    -- have : B_subst_a = B
    -- let BM := sorry
    -- let ih_f : TmM ΓM (PiM ΓM AM BM) ⟨f, _⟩ := Tm.rec' f sorry
    let ih_a : TmM ΓM AM ⟨ae, _⟩ := Tm.rec' ae sorry
    -- exact appM ΓM A AM B ih_f ih_a
    done
  | .lam body, w => sorry
  | .error, w => sorry

  def Con.rec' : (Γe : ECon) -> (Γw : WCon Γe) -> ConM ⟨Γe, Γw⟩
  | .nil, w => nilM
  | .ext Γe Ae, w =>
    let ih_Γ := Con.rec' Γe (let .ext Γw _ := w; Γw)
    let ih_A := Ty.rec' ih_Γ Ae (let .ext _ Aw := w; Aw)
    extM ih_Γ ih_A

  def Ty.rec' {Γ : Con} (ΓM : ConM Γ) : (Ae : ETy) -> (Aw : WTy Γ.fst Ae) -> TyM ΓM ⟨Ae, Aw⟩
  | ETy.U, w => sorry
  | .El t, w => sorry
  | .Pi Ae Be, w =>
    let AM : TyM .. := Ty.rec' ΓM Ae (let .Pi Aw Bw := w; Aw)
    let BM : TyM .. := Ty.rec' (extM ΓM AM) Be (let .Pi Aw Bw := w; Bw) -- how the fuck does lean just... accept termination for this? with no massaging? wow
    PiM ΓM AM BM

  def Subst.rec' {Γ : Con} (ΓM : ConM Γ) {Δ : Con} (ΔM : ConM Δ) : (σe : ESubst) -> (σw : WSubst Γ.fst Δ.fst σe) -> SubstM ΓM ΔM ⟨σe, σw⟩
  | .nil, w => sorry -- substNilM ΓM --(let .nil := w; sorry)
  | .cons σe te, w => sorry
end

def Con.rec (Γ : Con) : ConM Γ := Con.rec' (SubstM := SubstM) nilM extM PiM Γ.fst Γ.snd
def Ty.rec {Γ : Con} (ΓM : ConM Γ) (A : Ty Γ) : TyM ΓM A := Ty.rec' (SubstM := SubstM) nilM extM PiM ΓM A.fst A.snd
def Subst.rec {Γ : Con} (ΓM : ConM Γ) {Δ : Con} (ΔM : ConM Δ) (σ : Subst Γ Δ) : SubstM ΓM ΔM σ := Subst.rec' nilM extM PiM ΓM ΔM σ.fst σ.snd

-- theorem Subst.cons_β : Subst.rec nilM extM PiM ΓM ΔM (Subst.cons σ t) = consM ... := sorry
