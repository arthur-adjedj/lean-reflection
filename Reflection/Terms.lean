import Aesop
import Reflection.Util.Vec
import Reflection.Util.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic

set_option linter.unusedVariables false
-- set_option pp.fieldNotation.generalized false


@[aesop unsafe]
theorem Fin.ext' : @Eq (Fin (n+1)) ⟨1,h⟩ 1 := by ext; simp [Nat.mod_eq_of_lt h]

-- move to own util file later:
@[aesop unsafe, simp]
theorem Fin.add_val_pull {n : Fin (N + 1)} (h : n < N) : @Fin.val (N + 1) (n + 1) = (@Fin.val (N + 1) n) + 1 := by
  simp_all only [Fin.val_add_one_of_lt, natCast_eq_last, Nat.succ_eq_add_one]


mutual
  @[aesop unsafe]
  inductive ConE : Type
  | nil : ConE
  | ext : ConE -> TyE -> ConE
  deriving Repr, Inhabited

  /-- `Ty : Con -> Type` -/
  @[aesop unsafe]
  inductive TyE : Type
  /-- `U Γ : Ty Γ` -/
  | U : ConE -> TyE
  /-- `El {Γ} : (t : Tm Γ U) -> Ty Γ` -/
  | El : ConE -> TmE -> TyE
  /-- `Pi {Γ} : (A : Ty Γ) -> (B : Ty (Γ, A)) -> Ty Γ` -/
  | Pi : (Γ : ConE) -> (A : TyE) -> (B : TyE) -> TyE
  deriving Repr, Inhabited

  /-- `Var : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop unsafe]
  inductive VarE : Type
  /-- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]`, note that `wki : (Γ, A) <- Γ`, and `@wki Γ A = wkn (Γ, A) 1`, and `wki = wk id`. -/
  | vz : (Γ : ConE) -> (A : TyE) -> VarE
  /-- `vs {Γ} ~~{A : Ty Γ}~~ {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]`, but note that `wki` is a shorthand for `wkn (Γ, B) 1 : (Γ, B) <- Γ` -/
  | vs : (Γ : ConE) -> (B : TyE) -> VarE -> VarE
  deriving Repr, Inhabited

  /-- `Tm : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop unsafe]
  inductive TmE : Type
  /-- `var {Γ} ~~{A : Ty Γ}~~ : Var Γ A -> Tm Γ A` -/
  | var : (Γ : ConE) -> VarE -> TmE
  /-- `app {Γ : Con} {A : Ty Γ} {B : Ty (Γ, A)} : (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[id, a]`.\
    Note that the substitution `(id, a) : Γ <- (Γ, A)` intuitively instantiates de-Brujin variable #0 with `a : Tm Γ A`.  -/
  | app : (Γ : ConE) -> (A : TyE) -> (B : TyE) -> (f : TmE) -> (a : TmE) -> TmE
  /-- `lam {Γ} {A : Ty Γ} {B : Ty (Γ, A)} : (body : Tm (Γ, A) B) -> Tm Γ (Pi A B)` -/
  | lam : (Γ : ConE) -> (A : TyE) -> (B : TyE) -> (body : TmE) -> TmE
  /-- Only necessary because of substVarE. Will be proven impossible in the final IIRT. -/
  | error : TmE
  deriving Repr, Inhabited

  /-- A substitution `σ : Γ <- Δ` maps every variable in `Δ` to a `Γ`-term.
    Intuitively, it is a list of length `Δ.length` storing terms typed in context `Γ`. -/
  @[aesop unsafe]
  inductive SubstE : Type
  /-- `Subst.nil {Γ} : Γ <- ⬝` -/
  | nil : (Γ : ConE) -> SubstE
  /-- `Subst.cons {Γ} {Δ} {A : Ty Δ} : (δ : Γ <- Δ) -> (t : Tm Γ A[δ]) -> (Γ <- (Δ, A))` -/
  | cons : (Γ : ConE) -> (Δ : ConE) -> (A : TyE) -> SubstE -> TmE -> SubstE
  deriving Repr, Inhabited
end

@[aesop unsafe] def ConE.len : ConE -> Nat
| .nil => 0
| .ext Γ A => 1 + Γ.len
termination_by structural Γ => Γ
notation "∣" Γ:60 "∣" => ConE.len Γ

@[aesop unsafe] def VarE.idxΓ : VarE -> ConE
| .vz Γ .. => Γ
| .vs Γ .. => Γ

/-- Variables are de-Brujin variables. Given `.vs (.vs .vz)`, return `2`. -/
@[aesop unsafe] def VarE.deBrujin : VarE -> Nat
| .vz .. => 0
| .vs _ _ v => 1 + v.deBrujin

-- This is not provable, because `v.Γ` is arbitrary, since it is not constrained by type indices in the erased version:
-- @[aesop unsafe] theorem VarE.h_val : (v : VarE) -> v.val < ∣v.Γ∣
-- | .vz .. => ...
-- | .vs _ _ _ v => ...

@[aesop unsafe] def SubstE.len : SubstE -> Nat
| .nil Γ => 0
| .cons Γ Δ A σ t => 1 + σ.len
notation "∣" σ:60 "∣" => SubstE.len σ
example : ∣SubstE.nil Γ∣ = 0 := SubstE.len.eq_1 Γ -- doesn't work by rfl :(

@[aesop unsafe] def SubstE.Δ : SubstE -> ConE
| .nil Γ => .nil
| .cons Γ Δ A _ _ => .ext Δ A
@[aesop unsafe] def SubstE.Γ : SubstE -> ConE
| .nil Γ => Γ
| .cons Γ Δ _ _ _ => Γ

def ConE.drop.impl (Γ : ConE) : (n : Nat) -> n < Γ.len + 1 -> ConE
| 0  , h => Γ
| n+1, h => match Γ with
  | .nil => .nil
  | .ext Γ A => ConE.drop.impl Γ n (by rw [len] at h; omega)
termination_by structural n => n

/-- Notation: `Γ ─ n`. Drop the last `n` variables in the context.
  Example: `drop (Con.nil, A, B, C) 1 ≡ (Con.nil, A, B)`. -/
abbrev ConE.drop (Γ : ConE) (n : Fin (Γ.len + 1)) : ConE := ConE.drop.impl Γ n.1 n.2
notation Γ:70 " ─ " n:70 => ConE.drop Γ n

example : ConE.drop.impl (.ext Γ A) 1 (by rw [ConE.len]; omega) = Γ := rfl
example : ConE.drop (.ext Γ A) ⟨1, h⟩ = Γ := rfl -- It's important for this to work by rfl
-- ? Can we make this work by rfl too?
-- example : ConE.drop (.ext Γ A)  1     = Γ := by
--   unfold OfNat.ofNat
--   unfold Fin.instOfNatOfNeZeroNat
--   simp [Fin.ofNat']
--   aesop
--   rfl
--   done

section
  set_option allowUnsafeReducibility true
  attribute [semireducible] ConE.drop
  attribute [reducible] ConE.drop
  attribute [semireducible] ConE.drop.impl
  attribute [reducible] ConE.drop.impl
end

/-- Notation: `Γᵥ`. Get the type of the de-Brujin variable `v`.
   `get : (Γ : Con) -> (v : Fin Γ.len) -> Ty (drop Γ (v+1))`. -/
@[aesop unsafe] def ConE.get : (Γ : ConE) -> (v : Fin Γ.len) -> TyE
| .nil    , v => Fin.elim0 v
| .ext Γ A, ⟨0  , h⟩ => A
| .ext Γ A, ⟨v+1, h⟩ => -- expected `Ty (drop (Γ, A) (v+1+1))`
  -- ! theorem drop_ext : drop (Γ, A) (v+1+1) = drop Γ (v+1)
  Γ.get ⟨v, by rw [len] at h; linarith⟩ -- : Ty (drop Γ (v+1))

/-- Substitutions are essentially just lists of terms. So get the term stored at position `v`. -/
@[aesop unsafe] def SubstE.get : (σ : SubstE) -> (v : Fin σ.len) -> TmE
| .nil Γ, v => Fin.elim0 (SubstE.len.eq_1 _ ▸ v)
| .cons _ _ _ σ t, ⟨0  , h⟩ => t
| .cons _ _ _ σ t, ⟨v+1, h⟩ => σ.get ⟨v, by rw [len] at h; linarith⟩

/-- Look up the term stored in a substitution. -/
@[aesop unsafe] def substVarE : VarE -> SubstE -> TmE
| .vz _ _  , .cons _ _ _ _ t => t
| .vs _ _ v, .cons _ _ _ σ _ => substVarE v σ
| _, _ => .error

#check Fin.castSucc
#check Fin.val_add_one_of_lt

/-- If `n` is not the last element, we can add one without wrapping around. -/
abbrev Fin.addOne (n : Fin (N+1)) (h : n.val < N) : Fin (N+1) := ⟨n.val + 1, by simp_all only [add_lt_add_iff_right]⟩

mutual
  /-- `wkn {Γ : Con} (n : Fin (Γ.len + 1)) : (Γ <- Γ - n)` -/
  abbrev wknE (Γ : ConE) (n : Fin (Γ.len + 1)) : SubstE :=
    if h : Γ.len = n then .nil Γ
    else
      have h : n.1 < ∣Γ∣ := by omega
      SubstE.cons
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
  abbrev mkVarE : (Γ : ConE) -> (v : Fin Γ.len) -> VarE
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
      --   (Γ.drop ⟨v+1, by rw [ConE.len] at h; linarith⟩)
      --   (Γ.get ⟨v, by rw [ConE.len] at h; linarith⟩) -- `Γᵥ`
      --   (wkn (.ext Γ X) ⟨v+1+1, by simp_all only [ConE.len, add_lt_add_iff_right]⟩) -- `wkn (Γ, X) (v+1+1)`
      -- ) -- `Γᵥ[wkn (Γ, X) (v+1+1)]`
      X
      (mkVarE Γ ⟨v, by rw [ConE.len] at h; linarith⟩) -- `mkVar Γ v : Var Γ (Γ.get v)[wkn Γ (v+1)]`
  termination_by Γ v => sizeOf Γ
end

#print axioms wknE

/-- Identity substitution. `id : {Γ : Con} -> (Γ <- Γ)`. Just a shorthand for `wkn Γ 0`. -/
def idE (Γ : ConE) : SubstE := wknE Γ 0

/-- Weakened identity substitution. `wki : {Γ : Con} -> {W : Ty Γ} -> (Γ, W <- Γ)`. Just a shorthand for `wkn (Γ, W) 1`. -/
def wkiE (Γ : ConE) (W : TyE) : SubstE := wknE (.ext Γ W) ⟨1, by rw [ConE.len]; omega⟩

mutual
  /-- `substTy {Γ Δ : Con} (A : Ty Δ) (σ : Γ <- Δ) : Ty Γ` -/
  def substTyE (Γ Δ : ConE) : TyE -> SubstE -> TyE
  | .U Δ, σ => .U Γ
  | .El Δ t, σ => .El Γ (substTmE Γ Δ t σ)
  | .Pi Δ A B, σ => -- Δ ⊢ A
    let Aσ : TyE /- Γ -/ := substTyE Γ Δ A σ -- `Γ ⊢ A[σ]`
    have WRONG : sizeOf σ < 1 + sizeOf Δ + sizeOf A + sizeOf B := sorry
    let wk_σ /- : (Γ, A[σ]) <- Δ -/ := compE (.ext Γ Aσ) Γ Δ σ (wknE (.ext Γ Aσ) 1) -- note that `wk σ = σ ∘ (wkn (Γ, A[σ]) 1)`
    -- let A_wk_σ : TyE := substTyE (.ext Γ Aσ) Δ A wk_σ -- `(Γ, A[σ]) ⊢ A[wk σ]`
    let vz : TmE /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ Aσ) (.vz Γ Aσ) -- `.vz Γ A' : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = σ ∘ (wk id)`
    let δ : SubstE /- (Γ, A[σ]) <- (Δ, A) -/ := .cons (.ext Γ Aσ) Δ A (wk_σ) vz
    .Pi Γ Aσ (substTyE (.ext Γ Aσ) (.ext Δ A) B δ)
  termination_by A σ => sizeOf A --sizeOf A + sizeOf σ

  /-- `substTm {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ (substTy A σ)` -/
  def substTmE (Γ Δ : ConE) : TmE -> SubstE -> TmE
  | .var _ v, σ => substVarE v σ -- just pick the term in the subst that v refers to. if ill-formed, then .error.
  | .app _Δ A B f a, σ => -- `Δ ⊢ a : A`, `Δ ⊢ f : Pi A B`, expected `Tm Γ B[id, a][σ]`    (yes this `A` is the same as the `A` in `@substTm _ _ A ..`)
    let Aσ : TyE /- Γ -/ := substTyE Γ Δ A σ -- Γ ⊢ A[σ]
    -- let wk_σ : SubstE := wkE Γ Δ A' σ -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wk id)`
    have WRONG : sizeOf σ < 1 + sizeOf _Δ + sizeOf A + sizeOf B + sizeOf f + sizeOf a := sorry
    let wk_σ : SubstE := compE (.ext Γ Aσ) Γ Δ σ (wknE (.ext Γ Aσ) 1) -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wkn (Γ, A[σ]) 1)`
    -- let A_wk_σ : TyE /- (Γ, A[σ]) -/ := substTyE (.ext Γ Aσ) Δ A wk_σ -- A[wk σ]
    let vz : TmE /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ Aσ) (.vz Γ Aσ) -- `.vz Γ A[σ] : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = (wk id) ∘ σ`
    let δ : SubstE /- (Γ, A[σ]) <- (Δ, A) -/ := SubstE.cons (.ext Γ Aσ) Δ A (wk_σ) vz

    let B' : TyE := substTyE (.ext Γ Aσ) (.ext Δ A) B δ
    let f' : TmE := substTmE Γ Δ f σ -- `f[σ] : Tm Γ (Pi A B)[σ]`, where `(Pi A B)[σ] = Pi A[σ] B[wk σ, #0]` per definition of substTy
    let a' : TmE := substTmE Γ Δ a σ -- `a[σ] : Tm Γ A[σ]`
    let fa' : TmE := .app Γ Aσ B' f' a' -- `.app f[σ] a[σ] : Tm Γ B[wk σ, #0][id, a]`
    fa' -- ! here we need `((wk σ), #0) ∘ (id, a) = (id, a) ∘ σ` to typecheck.
  | .lam Δ A B body, σ => .error
  | .error, _ => .error
  termination_by t σ => sizeOf t -- sizeOf t + sizeOf σ

  /-- `comp {Γ Θ Δ : Con} : Subst Θ Δ -> Subst Γ Θ -> Subst Γ Δ` -/
  def compE (Γ Θ Δ : ConE) : SubstE -> SubstE -> SubstE
  | .nil Θ         , σ => .nil Γ
  | .cons Θ Δ A δ t, σ => -- `δ : Θ <- Δ`,   `σ : Γ <- Θ`,   `Θ ⊢ t : A[δ]`,   expected `Γ <- Δ, A`
    .cons Γ Δ A
      (compE Γ Θ Δ δ σ) -- δ ∘ σ : Γ <- Δ
      (substTmE Γ Θ t σ) -- `Γ ⊢ t[σ] : A[δ][σ]`, -- ! need theorem `A[δ][σ] = A[δ ∘ σ]`
  termination_by δ σ => sizeOf δ -- sizeOf δ + sizeOf σ
end

/-- `wk : {Γ Δ : Con} -> {W : Ty Γ} -> (Γ <- Δ) -> (Γ, W <- Δ)` -/
def wkE (Γ Δ : ConE) (W : TyE) (σ : SubstE) : SubstE
  := compE (.ext Γ W) Γ Δ σ (wkiE Γ W) -- `wki : Γ,W <- Γ`

/-- Parellel weakening `wkp {Γ Δ} {A : Ty Δ} (σ : Γ <- Δ) : (Γ, A[σ]) <- (Δ, A)`. This is the `δ` used in substTyE and substTmE. -/
def wkpE (Γ Δ : ConE) (A : TyE) (σ : SubstE) : SubstE :=
  let Aσ : TyE /- Γ -/ := substTyE Γ Δ A σ -- `Γ ⊢ A[σ]`
  let wk_σ : SubstE := compE (.ext Γ Aσ) Γ Δ σ (wknE (.ext Γ Aσ) 1) -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wkn (Γ, A[σ]) 1)`
  let vz : TmE /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ Aσ) (.vz Γ Aσ) -- `.vz Γ A[σ] : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = (wk id) ∘ σ`
  let δ : SubstE /- (Γ, A[σ]) <- (Δ, A) -/ := SubstE.cons (.ext Γ Aσ) Δ A wk_σ vz
  .cons (.ext Γ Aσ) Δ A wk_σ vz


@[simp] theorem Γ_len0_nil {Γ : ConE} {n : Fin (Γ.len + 1)} (h : Γ.len = 0) : Γ = .nil :=
  match Γ with
  | .nil => rfl
  | .ext Γ A => by rw [ConE.len] at h; rename_i Γ_1; simp_all only [add_eq_zero, one_ne_zero, false_and]

@[simp] theorem drop_0 : {Γ : ConE} -> Γ ─ 0 = Γ := rfl

@[simp] theorem drop_ext_1' : {Γ : ConE} -> {h : 1 < ∣Γ.ext A∣ + 1} -> .ext Γ A ─ ⟨1, h⟩ = Γ
| .nil    , _ => by simp_all only [Fin.mk_one, Fin.isValue]; --simp_all only [lt_add_iff_pos_left, Fin.isValue]; rfl
| .ext Γ A, h => rfl
-- @[simp] theorem drop_ext_1 : {Γ : ConE} -> .ext Γ A ─ 1 = Γ := by aesop?

@[simp] theorem drop_ext_1_n : {Γ : ConE} -> {h : _ < ∣Γ.ext A∣ + 1} -> {h' : _ < _} -> .ext Γ A ─ ⟨n+1, h⟩ = Γ ─ ⟨n, h'⟩
| .nil    , _ => rfl
| .ext Γ A, h => rfl

@[simp] theorem drop_all {Γ : ConE} {n : Fin (Γ.len + 1)} (h : Γ.len = n) : Γ ─ n = .nil :=
  match Γ, n with
  | Γ, 0 => by
    rw [Γ_len0_nil h, drop_0]
    exact 0 -- this is so weird?
  | .ext Γ A, ⟨.succ n, hsn⟩ => by
    rw [ConE.drop]
    exact @drop_all Γ ⟨n, by simp_all only [ConE.len, Nat.succ_eq_add_one]; rw [add_comm, h]; simp⟩
      (by -- ugly proof
        simp_all only
        simp_all only [Nat.succ_eq_add_one, lt_add_iff_pos_right, zero_lt_one]
        rw [ConE.len.eq_2] at h
        omega)

@[simp] theorem wknE_all {Γ : ConE} {n : Fin (Γ.len + 1)} (h : Γ.len = n) : wknE Γ n = .nil Γ := by
  rw [wknE]
  simp only [dite_eq_left_iff, imp_false, Decidable.not_not]
  intro h_1
  simp_all only

/-- `(Γ - (v+1), Γᵥ) = Γ - v` -/
@[simp]
theorem con_ext_get' (Γ : ConE) (v : Fin Γ.len) (h1 : ↑v + 1 < ∣Γ∣ + 1) (h2 : ↑v < ∣Γ∣) (h' : ↑v < ∣Γ∣ + 1)
  : .ext (Γ ─ ⟨v+1, h1⟩) (Γ.get ⟨v, h2⟩)    =    Γ ─ ⟨v, h'⟩
  := by
  match Γ, v with
  | .nil    , n => exact Fin.elim0 n
  | .ext Γ A, ⟨0  , h⟩ => simp only [zero_add, drop_ext_1', ConE.get, Fin.zero_eta, drop_0]
  | .ext Γ A, ⟨v+1, h⟩ =>
    have ih := con_ext_get' Γ ⟨v, by rw [ConE.len] at h; omega⟩ (by omega) (by omega) (by omega)
    simp only [ConE.drop, ConE.get, ih]

-- theorem con_ext_get (Γ : ConE) (v : Fin Γ.len) : .ext (Γ ─ v.succ) (Γ.get v) = Γ ─ v.castSucc := by sorry -- con_ext_get'

@[simp] theorem get_0 (Γ : ConE) (A : TyE) {h : 0 < ∣Γ.ext A∣} : (Γ.ext A).get ⟨0, h⟩ = A := by rw [ConE.get]

/-- `get (Γ, X) (v+1) = get Γ v` -/
@[simp] theorem get_ext_1 (Γ : ConE) (A : TyE) (v) {h : _ < _} {h'} : (Γ.ext A).get ⟨v+1, h⟩ = Γ.get ⟨v, h'⟩ := by rw [ConE.get]


section Tests
  def F'' : TyE := .Pi (.nil) (.U .nil) (.U .nil)
  def Γe'' : ConE := .ext (.ext (.ext (.ext .nil (.U .nil)) F'') F'') F''
  #reduce sizeOf <| idE Γe''
  -- #reduce sizeOf <| wkpE Γe'' Γe'' F'' <| idE Γe''

  #eval idE .nil
  #reduce sizeOf (idE .nil)
  #reduce sizeOf (idE (.ext .nil (.U .nil)))

  #eval idE (.ext .nil (.U .nil))
  #eval idE (.ext (.ext .nil (.U .nil)) (.U .nil))
  #eval idE (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

  def wk1 (Γ : ConE) : SubstE := wknE Γ 1
  #eval wk1 (.ext .nil (.U .nil))
  #eval wk1 (.ext (.ext .nil (.U .nil)) (.U .nil))
  #eval wk1 (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

  def wk2 (Γ : ConE) : SubstE := wknE Γ 2
  #eval wk2 (.ext (.ext .nil (.U .nil)) (.U .nil))
  #eval wk2 (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

  -- #eval wkpE Γe Γe (.U Γe) <| idE Γe
end Tests


/-- `def idxA : Var Γ A -> Ty Γ := A`. Reconstruct the `A` in `Var Γ A`. -/
noncomputable def VarE.idxA : VarE -> TyE
| .vz Γ A => A
| .vs Γ B v => -- `.vs v : Var (Γ, B) A[wkn (Γ, B) 1]`, and `v : Var A Γ`, and ~~`Γ⊢A`~~, and `Γ,A⊢B`, expecting `Ty (Γ, B)`.
  let A := v.idxA -- `Γ ⊢ A`
  -- let A_wk := A[wkn (.ext Γ B) 1] Γ (.ext Γ B)  -- `Γ, B ⊢ A[wkn (Γ, B) 1]`
  let A_wk := substTyE Γ (.ext Γ B) A (wknE (.ext Γ B) 1) -- `Γ, B ⊢ A[wkn (Γ, B) 1]`
  A_wk

-- /-- Reconstruct the `A` in `Tm Γ A`. -/
-- noncomputable def TmE.idxA : TmE -> TyE
-- | .var Γ v => v.idxA
-- | .app Γ A B f a => A -- this is the one spot where we *need* to store `A`. Intuitively, `.app` is modus ponens, so similar to cuts in sequent calculus. We can't do cut elimination in Lean afaik, so we are unable to Reconstruct `A` here.
-- | .lam .. => sorry
-- | .error .. => sorry

#check VarE.idxA

mutual
  @[aesop unsafe constructors cases]
  inductive ConW : ConE -> Prop
  | nil : ConW .nil
  | ext : (Γw : ConW Γ) -> (Aw : TyW Γ A) -> ConW (.ext Γ A)

  @[aesop unsafe constructors cases]
  inductive TyW : ConE -> TyE -> Prop
  | U : ConW Γ -> TyW Γ (.U Γ)
  | El : ConW Γ -> TmW Γ (.U Γ) t -> TyW Γ (.El Γ t)
  | Pi : ConW Γ -> TyW Γ A -> TyW (.ext Γ A) B -> TyW Γ (.Pi Γ A B)
  /-- A mutual inductive type which may refer to existing types in Γ, and has type A. -/
  -- | mind : MInd /- Γ -/ A -> Ty Γ

  -- @[aesop constructors cases]
  -- inductive VarW : ConE -> TyE -> VarE -> Prop
  -- /- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]` -/
  -- | vz : ConW Γ -> TyW Γ A -> VarW (.ext Γ A) (substTyE (.ext Γ A) Γ A (wkiE Γ A)) (.vz Γ A)
  -- /- `vs {Γ} ~~{A : Ty Γ}~~ {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]` -/
  -- | vs : ConW Γ -> TyW Γ A -> TyW Γ B -> VarW Γ A v
  --   -> VarW (.ext Γ B) (substTyE (.ext Γ B) Γ A (wkiE Γ B)) (.vs Γ /- ~~A~~ -/ B v)

  @[aesop unsafe constructors cases]
  inductive VarW : ConE -> TyE -> VarE -> Prop
  /- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]` -/
  | vz : ConW Γ -> TyW Γ A -> VarW (.ext Γ A) (substTyE (.ext Γ A) Γ A (wkiE Γ A)) (.vz Γ A)
  /- `vs {Γ} ~~{A : Ty Γ}~~ {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]` -/
  | vs {Γ A B v} : ConW Γ -> /-~~ TyW Γ A -> ~~-/ TyW Γ B -> VarW Γ A v
    -> VarW (.ext Γ B) (substTyE (.ext Γ B) Γ A (wkiE Γ B)) (.vs Γ /- ~~A~~ -/ B v)

  @[aesop unsafe constructors cases]
  inductive TmW : ConE -> TyE -> TmE -> Prop
  /- var {Γ} ~~{A : Ty Γ}~~ : Var Γ A -> Tm Γ A -/
  | var : ConW Γ -> /- ~~ TyW Γ A -> ~~-/ VarW Γ A v -> TmW Γ A (.var Γ /- ~~A~~ -/ v)
  /- `app {Γ : Con} {A : Ty Γ} {B : Ty (Γ, A)} : (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[id, a]`
    Here, `(id Γ, a)` is `Γ <- Γ, A`. -/
  | app : ConW Γ -> TyW Γ A -> TyW (.ext Γ A) B ->
    TmW Γ (.Pi Γ A B) f ->
    TmW Γ A a ->
    TmW Γ (substTyE Γ (.ext Γ A) B (.cons Γ Γ A (idE Γ) a)) (.app Γ A B f a)
  -- | lam : {Aw : TyW Γe Ae} ->
  --         {Bw : TyW (.ext Γe Ae) Be} ->
  --         (bodyw : TmW (.ext Γe Ae) Be bodye) ->
  --         TmW Γe (.Pi Ae Be) (.lam bodye)

  @[aesop unsafe constructors cases]
  inductive SubstW : ConE -> ConE -> SubstE -> Prop
  | nil : ConW Γ -> SubstW Γ .nil (.nil Γ)
  /- Subst.cons {Γ} {Δ} {A : Ty Δ} : (δ : Γ <- Δ) -> (t : Tm Γ A[δ]) -> (Γ <- (Δ, A)) -/
  | cons : ConW Γ -> ConW Δ -> TyW Δ A ->
      SubstW Γ Δ δ ->
      TmW Γ (substTyE Γ Δ A δ) t ->
      SubstW Γ (.ext Δ A) (.cons Γ Δ A δ t)
end

@[aesop unsafe] theorem dropW : (Γw : ConW Γ) -> (n : Fin (∣Γ∣+1)) -> ConW (Γ ─ n)
| ConW.nil    , ⟨0, _⟩ => .nil
| Γw, ⟨0  , h⟩ => Γw
| @ConW.ext Γ A Γw Aw, ⟨n+1, h⟩ => by rw [ConE.drop]; exact dropW Γw ⟨n, by rw [ConE.len] at h; omega⟩

@[aesop unsafe] theorem getW {Γ : ConE} : (Γw : ConW Γ) -> (v : Fin Γ.len) -> TyW (Γ ─ v.succ) (Γ.get v)
| .nil    , v => Fin.elim0 v
| @ConW.ext Γ A Γw Aw, ⟨0  , h⟩ => by simp only [Fin.succ_mk, Nat.succ_eq_add_one, zero_add, ConE.drop, drop_0, ConE.get]; exact Aw
| @ConW.ext Γ A Γw Aw, ⟨v+1, h⟩ => by simp [ConE.drop, ConE.get]; exact getW Γw ⟨v, by rw [ConE.len] at h; omega⟩

-- ! need theorem : wkn Γ (v+1) ∘ wkn (Γ, X) 1 = wkn (Γ, X) (v+1+1)
-- `substTyE_comp {δ : Subst Θ Δ} {σ : Subst Γ Θ} : substTy (substTy A δ) σ = substTy A (δ ∘ σ)`
#check compE
#check substTyE

mutual
  @[simp] theorem substTyE_comp (δ σ : SubstE) : substTyE Γ Θ (substTyE Θ Δ A δ) σ = substTyE Γ Δ A (compE Γ Θ Δ δ σ) := by
    match A with
    | .U _Δ => rw [substTyE, substTyE, substTyE]
    | .El _Δ t => -- ⊢ substTyE Γ Θ (substTyE Θ Δ (TyE.El _Δ t) δ) σ = substTyE Γ Δ (TyE.El _Δ t) (compE Γ Θ Δ δ σ)
      rw [substTyE, substTyE, substTyE] -- ⊢ TyE.El Γ (substTmE Γ Θ (substTmE Θ _Δ t δ) σ) = TyE.El Γ (substTmE Γ _Δ t (compE Γ Θ Δ δ σ))
      rw [substTmE_comp]
      -- ⊢   TyE.El Γ (substTmE Γ _Δ t (compE Γ Θ _Δ δ σ))
      --   = TyE.El Γ (substTmE Γ _Δ t (compE Γ Θ Δ δ σ))       -- note that Δ is not quite _Δ
      have : _Δ = Δ := sorry -- ! argh this might be impossible to show in the erased version...
      rw [this]
    | .Pi _Δ A B =>
      have ih_A : substTyE Γ Θ (substTyE Θ Δ A δ) σ = substTyE Γ Δ A (compE Γ Θ Δ δ σ) := substTyE_comp _ _
      -- ! ih_B should not be provable, the indices are wrong
      have ih_B : substTyE Γ Θ (substTyE Θ Δ B δ) σ = substTyE Γ Δ B (compE Γ Θ Δ δ σ) := substTyE_comp _ _
      have : _Δ = Δ := sorry
      rw [substTyE, substTyE, substTyE]
      sorry

  @[simp] theorem substTmE_comp (δ σ : SubstE) : substTmE Γ Θ (substTmE Θ Δ t δ) σ = substTmE Γ Δ t (compE Γ Θ Δ δ σ) := by
    sorry
end

#exit

-- set_option pp.proofs true in
set_option pp.explicit true in
mutual
  /-- `wkn {Γ : Con} (n : Fin (Γ.len + 1)) : (Γ <- Γ - n)` -/
  def wknW (Γw : ConW Γ) (n : Fin (Γ.len + 1)) : SubstW Γ (Γ ─ n) (wknE Γ n) := by
    -- SubstW.nil {Γe : ConE} : ConW Γe → SubstW ConE.nil Γe (SubstE.nil Γe)
    if h : Γ.len = n then
      rw [wknE_all h, drop_all h]
      exact @SubstW.nil Γ Γw
      done
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
      simp [ConE.drop, Fin.addOne] at this
      let v : Fin Γ.len := ⟨n, by omega⟩ -- maybe adapting `con_ext_get'` makes more sense than introducing this v
      have rw := con_ext_get' Γ v (by omega) (by omega) (by omega)
      rw [rw] at this
      rw [wknE]
      simp_all only [Fin.eta, ↓reduceDIte]

  -- `mkVar : (Γ : Con) -> (v : Fin Γ.len) -> Var Γ Γₙ[wkn Γ (v+1)]`
  def mkVarW : (Γw : ConW Γ) -> (v : Fin Γ.len) ->
    VarW Γ (substTyE Γ (Γ ─ ⟨v.val + 1, by omega⟩) (Γ.get ⟨v.val, by omega⟩) (wknE Γ v.succ)) (mkVarE Γ v)
  | .nil, v => Fin.elim0 v
  | @ConW.ext Γ X Γw Xw, ⟨0  , h⟩ => by -- expected `Var (Γ, X) (get (Γ, X) 0)[wkn (Γ, X) (0 + 1)]`
    -- by defeq we have `get (Γ, X) 0 ≡ X`
    rw [mkVarE]
    simp [Fin.addOne]
    have := VarW.vz Γw Xw
    rw [wkiE] at this
    -- have rw := @Fin.eta (∣Γ.ext X∣ + 1) 1 (by omega)
    have h : 1 < ∣Γ.ext X∣ + 1 := by omega
    have : ⟨1, h⟩ = (1 : Fin (∣Γ.ext X∣ + 1)) := by
      ext
      simp [Nat.mod_eq_of_lt h]
      done
    simp_all only [Nat.succ_eq_add_one]
  | @ConW.ext Γ X Γw Xw, ⟨v+1, h⟩ => by -- expected `Var (Γ, X) (get (Γ, X) (v+1))[wkn (Γ, X) (v + 1 + 1)]`
    rw [ConE.len] at h
    -- simp
    rw [drop_ext_1_n (h := by omega)]
    simp
    rw [get_ext_1]

    let varr := mkVarE Γ ⟨v, by omega⟩
    let A := varr.idxA

    have ih := mkVarW Γw ⟨v, by omega⟩
    simp at ih

    -- ! need theorem : A[σ][δ] = A[σ ∘ δ]

    -- ! need theorem : wkn Γ (v+1) ∘ wkn (Γ, X) 1 = wkn (Γ, X) (v+1+1)
    --                  ^^^^^^^^^^^^^^^^^^^^^^^^^^                         this is (part of) the resulting type we get from `Var.vs`
    --                                               ^^^^^^^^^^^^^^^^^^    this is (part of) the expected type for this match arm.

    -- TODO finish this proof
    /- VarW.vs {Γ : ConE} {~~A~~ B : TyE} {v : VarE} : ConW Γ → TyW Γ A → TyW Γ B → VarW Γ A v → VarW (Γ.ext B) (substTyE (Γ.ext B) Γ A (wkiE Γ B)) (VarE.vs Γ B v)-/
    have := VarW.vs (A := varr.idxA) Γw /-~~ A[wki] ~~-/ Xw ih
    -- exact this
    done
end

-- TODO:
mutual
  /-- `substTy {Γ Δ : Con} (A : Ty Δ) (σ : Subst Γ Δ) : Ty Γ` -/
  def substTyW (Γw : ConW Γ) (Δw : ConW Δ) (Aw : TyW Δ A) (σw : SubstW Γ Δ σ) : TyW Γ (substTyE Γ Δ A σ) := sorry
  /-- `substTm {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ (substTy A σ)` -/
  def substTmW (Γw : ConW Γ) (Δw : ConW Δ) (Aw : TyW Δ A) (tw : TmW Δ A t) (σw : SubstW Γ Δ σ) : TmW Γ (substTyE Γ Δ A σ) (substTmE Γ Δ t σ) := sorry
  /-- `comp {Γ Θ Δ : Con} : Subst Θ Δ -> Subst Γ Θ -> Subst Γ Δ` -/
  def compW (Γw : ConW Γ) (Θw : ConW Θ) (Δw : ConW Δ) (δw : SubstW Θ Δ δ) (σw : SubstW Γ Θ σ) : SubstW Γ Δ (compE Γ Θ Δ δ σ) := sorry
end

def Con : Type                                                                               := @PSigma ConE ConW
def Ty (Γ : Con) : Type                                                                      := @PSigma TyE (TyW Γ.1)
def Var (Γ : Con) (A : Ty Γ) : Type                                                          := @PSigma VarE (VarW Γ.1 A.1)
def Tm (Γ : Con) (A : Ty Γ) : Type                                                           := @PSigma TmE (TmW Γ.1 A.1)
def Subst (Γ Δ : Con) : Type                                                                 := @PSigma SubstE (SubstW Γ.1 Δ.1)

abbrev Con.len (Γ : Con) : Nat                                                                  := Γ.1.len
abbrev Con.drop (Γ : Con) (n : Fin (Γ.len + 1)) : Con                                           := ⟨Γ.1.drop n, dropW Γ.2 n⟩
def Con.get (Γ : Con) (v : Fin Γ.len) : Ty (Γ.drop v.succ)                                   := ⟨Γ.1.get v, getW Γ.2 v⟩
def wkn {Γ : Con} (n : Fin (Γ.len + 1)) : Subst Γ (Γ.drop n)                                 := ⟨wknE Γ.1 n, wknW Γ.2 n⟩
def substTy {Γ Δ : Con} (A : Ty Δ) (σ : Subst Γ Δ) : Ty Γ                                    := ⟨substTyE Γ.1 Δ.1 A.1 σ.1, substTyW Γ.2 Δ.2 A.2 σ.2⟩
def substTm {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ (substTy A σ)         := ⟨substTmE Γ.1 Δ.1     t.1 σ.1, substTmW Γ.2 Δ.2 A.2 t.2 σ.2⟩
def comp {Γ Θ Δ : Con} (δ : Subst Θ Δ) (σ : Subst Γ Θ) : Subst Γ Δ                           := ⟨compE Γ.1 Θ.1 Δ.1 δ.1 σ.1, compW Γ.2 Θ.2 Δ.2 δ.2 σ.2⟩
notation δ:max " ∘ " σ:max => comp δ σ

/-- `mkVar : (Γ : Con) -> (v : Fin Γ.len) -> Var Γ  Γᵥ[wkn Γ (v+1)]` -/
def mkVar {Γ : Con} (v : Fin Γ.len) : Var Γ (substTy (Γ.get v) (wkn v.succ))                 := ⟨mkVarE Γ.1 v, mkVarW Γ.2 v⟩
notation "#" v => mkVar v

abbrev Con.nil : Con                                                                            := ⟨.nil, .nil⟩
abbrev Con.ext (Γ : Con) (A : Ty Γ) : Con                                                       := ⟨.ext Γ.fst A.fst, .ext Γ.snd A.snd⟩
def Ty.U : Ty Γ                                                                              := ⟨.U Γ.1, .U Γ.2⟩
def Ty.El (t : Tm Γ .U) : Ty Γ                                                               := ⟨.El Γ.1 t.fst, .El Γ.2 t.snd⟩
def Ty.Pi (A : Ty Γ) (B : Ty (.ext Γ A)) : Ty Γ                                              := ⟨.Pi Γ.1 A.fst B.fst, .Pi Γ.2 A.snd B.snd⟩
def Subst.nil : Subst Γ Con.nil                                                              := ⟨.nil Γ.1, .nil Γ.2⟩
def Subst.cons (δ : Subst Γ Δ) (t : Tm Γ (substTy A δ)) : Subst Γ (Δ.ext A)                  := ⟨.cons .., .cons Γ.2 Δ.2 A.2 δ.2 t.2⟩

abbrev Subst.id {Γ : Con} : Subst Γ Γ := wkn ⟨0, by unfold Con.len; unfold ConE.len; simp⟩
/-- Weakened identity substitution. `wki : {Γ : Con} -> {W : Ty Γ} -> (Γ, W <- Γ)`. Just a shorthand for `wkn (Γ, W) 1`. -/
abbrev wki {Γ : Con} {W : Ty Γ} : Subst (Γ.ext W) Γ := wkn ⟨1, by unfold Con.len; unfold ConE.len; simp⟩
/-- `wk : {Γ Δ : Con} -> {W : Ty Γ} -> (Γ <- Δ) -> (Γ, W <- Δ)` -/
abbrev wk {Γ Δ : Con} {W : Ty Γ} (σ : Subst Γ Δ) : Subst (Γ.ext W) Δ := σ ∘ wki

def substTy_E : (@substTy Γ Δ A σ).fst = substTyE Γ.1 Δ.1 A.1 σ.1 := rfl

/-- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]`. -/
def Var.vz : Var (Con.ext Γ A) (substTy A wki) := ⟨.vz Γ.1 A.1, by simp_all only [substTy_E]; exact VarW.vz Γ.2 A.2⟩ -- ? why does this reach max recursion depth without the simp_all lol
/-- `vs {Γ} ~~{A : Ty Γ}~~ {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]`, but note that `wki` is a shorthand for `wkn (Γ, B) 1 : (Γ, B) <- Γ` -/
-- set_option diagnostics true in
def Var.vs (v : Var Γ A) : Var (Con.ext Γ B) (substTy A wki) := ⟨.vs Γ.1     B.1 v.1, by simp_all [substTy_E]; exact .vs Γ.2      B.2 v.2⟩

mutual
-- set_option maxRecDepth 100
def substTy_id {A : Ty Γ} : substTy A Subst.id = A := by
  unfold Subst.id
  unfold wkn wknE
  simp
  aesop
  unfold substTy
  aesop
  -- -- unfold substTyE
  done
end

abbrev Subst.apply (a : Tm Γ A) : Subst Γ (Γ.ext A) := .cons .id (substTy_id ▸ a)

/-- It doesn't matter how we cast a term `t : Tm Γ A`, its erased term is the same. -/
def substTm_id_irrelevant {Γ : Con} {A : Ty Γ} {t : Tm Γ A} : ((substTy_id ▸ t) : Tm Γ (substTy A .id)).fst = t.fst := by
  sorry

def Tm.var {Γ} {A : Ty Γ} (v : Var Γ A) : Tm Γ A := ⟨TmE.var .., TmW.var Γ.2 v.2⟩

-- def Tm.app {A : Ty Γ} {B : Ty (Γ.ext A)} (f : Tm Γ (.Pi A B)) (a : Tm Γ A) : Tm Γ (substTy B (.cons .id (substTy_id ▸ a)))
/-- `Tm.app {A : Ty Γ} {B : Ty (Γ, A)} (f : Tm Γ (.Pi A B)) (a : Tm Γ A) : Tm Γ B[id, a]` -/
def Tm.app {A : Ty Γ} {B : Ty (Γ.ext A)} (f : Tm Γ (.Pi A B)) (a : Tm Γ A) : Tm Γ (substTy B (.apply a))
  := ⟨.app Γ.1 A.1 B.1 f.1 a.1, by
    rw [substTy_E]
    simp_all [Subst.apply, Subst.id]
    unfold wkn
    unfold Subst.cons
    have ret := TmW.app Γ.2 A.snd B.snd f.snd a.snd
    rw [idE] at ret
    simp [substTm_id_irrelevant]
    exact ret
  ⟩

def Con.ext_pull (Γ : Con) (A : Ty Γ) : (Γ.fst.ext A.fst) = (Γ.ext A).fst := rfl
def drop_ext_1 (Γ : Con) (W : Ty Γ) : (Γ.ext W).drop ⟨1, by simp [Con.len, ConE.len]⟩ = Γ := rfl

#check substTyE_comp
-- TODO: Prove these, but **not here**! Prove them about the -E version instead, then these will be trivial
@[simp] def Subst.substTy_comp {δ : Subst Θ Δ} {σ : Subst Γ Θ} : substTy (substTy A δ) σ = substTy A (δ ∘ σ) := by sorry
@[simp] def Subst.substTm_comp : substTm (substTm t σ) δ = substTy_comp.symm ▸ substTm t (σ ∘ δ) := sorry
@[simp] def Subst.comp_wki {σ : Subst Γ Δ} : σ ∘ (wki (W := W)) = wk σ := by sorry
@[simp] def Subst.substTy_wk_σ : substTy (substTy A σ) (wki (W := W)) = substTy A (wk σ) := by simp_all only [substTy_comp, comp_wki]

/-- Parellel weakening `wkp {Γ Δ} {A : Ty Δ} (σ : Γ <- Δ) : (Γ, A[σ]) <- (Δ, A)`. -/
abbrev wkp {Γ Δ} {A : Ty Δ} (σ : Subst Γ Δ) : Subst (Γ.ext (substTy A σ)) (Δ.ext A) :=
  .cons (wk σ) (.var (Subst.substTy_wk_σ ▸ Var.vz))


-- TODO: rest of the constructors (easy)

-- TODO: Some funky notation (and maybe remove the notation from the -E stuff, it won't be needed now)


-- # !
-- # Everything below this line is VERY out of date!

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
  def Tm.rec' {ΓM : ConM Γ} {AM : TyM ΓM A} : (te : TmE) -> (tw : WTm Γ.fst A.fst te) -> TmM ΓM AM ⟨te, tw⟩
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

  def Con.rec' : (Γe : ConE) -> (Γw : WCon Γe) -> ConM ⟨Γe, Γw⟩
  | .nil, w => nilM
  | .ext Γe Ae, w =>
    let ih_Γ := Con.rec' Γe (let .ext Γw _ := w; Γw)
    let ih_A := Ty.rec' ih_Γ Ae (let .ext _ Aw := w; Aw)
    extM ih_Γ ih_A

  def Ty.rec' {Γ : Con} (ΓM : ConM Γ) : (Ae : TyE) -> (Aw : WTy Γ.fst Ae) -> TyM ΓM ⟨Ae, Aw⟩
  | TyE.U, w => sorry
  | .El t, w => sorry
  | .Pi Ae Be, w =>
    let AM : TyM .. := Ty.rec' ΓM Ae (let .Pi Aw Bw := w; Aw)
    let BM : TyM .. := Ty.rec' (extM ΓM AM) Be (let .Pi Aw Bw := w; Bw) -- how the fuck does lean just... accept termination for this? with no massaging? wow
    PiM ΓM AM BM

  def Subst.rec' {Γ : Con} (ΓM : ConM Γ) {Δ : Con} (ΔM : ConM Δ) : (σe : SubstE) -> (σw : WSubst Γ.fst Δ.fst σe) -> SubstM ΓM ΔM ⟨σe, σw⟩
  | .nil, w => sorry -- substNilM ΓM --(let .nil := w; sorry)
  | .cons σe te, w => sorry
end

def Con.rec (Γ : Con) : ConM Γ := Con.rec' (SubstM := SubstM) nilM extM PiM Γ.fst Γ.snd
def Ty.rec {Γ : Con} (ΓM : ConM Γ) (A : Ty Γ) : TyM ΓM A := Ty.rec' (SubstM := SubstM) nilM extM PiM ΓM A.fst A.snd
def Subst.rec {Γ : Con} (ΓM : ConM Γ) {Δ : Con} (ΔM : ConM Δ) (σ : Subst Γ Δ) : SubstM ΓM ΔM σ := Subst.rec' nilM extM PiM ΓM ΔM σ.fst σ.snd

-- theorem Subst.cons_β : Subst.rec nilM extM PiM ΓM ΔM (Subst.cons σ t) = consM ... := sorry
