import Aesop
import Reflection.Util.Vec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
set_option pp.fieldNotation.generalized false

mutual
  @[aesop unsafe constructors cases]
  inductive ECon : Type
  | nil : ECon
  | ext : ECon -> ETy -> ECon
  deriving Repr, Inhabited

  /-- `Ty : Con -> Type` -/
  @[aesop unsafe constructors cases]
  inductive ETy : Type
  /-- `U Γ : Ty Γ` -/
  | U : ECon -> ETy
  /-- `El {Γ} : (t : Tm Γ U) -> Ty Γ` -/
  | El : ECon -> ETm -> ETy
  /-- `Pi {Γ} : (A : Ty Γ) -> (B : Ty (Γ, A)) -> Ty Γ` -/
  | Pi : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> ETy
  deriving Repr, Inhabited

  /-- `Var : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop unsafe constructors cases]
  inductive EVar : Type
  /-- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]`, note that `wki : (Γ, A) <- Γ`, and `@wki Γ A = wkn (Γ, A) 1`, and `wki = wk id`. -/
  | vz : (Γ : ECon) -> (A : ETy) -> EVar
  /-- `vs {Γ} {A B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]`, but note that `wki` is a shorthand for `wkn (Γ, B) 1 : (Γ, B) <- Γ` -/
  | vs : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> EVar -> EVar
  deriving Repr, Inhabited

  /-- `Tm : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop unsafe constructors cases]
  inductive ETm : Type
  /-- `var {Γ} {A : Ty Γ} : Var Γ A -> Tm Γ A` -/
  | var : (Γ : ECon) -> (A : ETy) -> EVar -> ETm
  /-- `app {Γ} : {A : Ty Γ} -> {B : Ty (Γ, A)} -> (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[id, a]`.\
    Note that the substitution `(id, a) : Γ <- (Γ, A)` intuitively instantiates de-Brujin variable #0 with `a : Tm Γ A`.  -/
  | app : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> (f : ETm) -> (a : ETm) -> ETm
  /-- `lam {Γ} : {A : Ty Γ} -> {B : Ty (Γ, A)} -> (body : Tm (Γ, A) B) -> Tm Γ (Pi A B)` -/
  | lam : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> (body : ETm) -> ETm
  /-- Only necessary because of substVarE. Will be proven impossible in the final IIRT. -/
  | error : ETm
  deriving Repr, Inhabited

  /-- A substitution `σ : Γ <- Δ` maps every variable in `Δ` to a `Γ`-term.
    Intuitively, it is a list of length `Δ.length` storing terms typed in context `Γ`. -/
  @[aesop unsafe constructors cases]
  inductive ESubst : Type
  /-- `Subst.nil {Γ} : Γ <- ⬝` -/
  | nil : (Γ : ECon) -> ESubst
  /-- `Subst.cons {Γ} {Δ} {A : Ty Δ} : (δ : Γ <- Δ) -> (t : Tm Γ A[δ]) -> (Γ <- (Δ, A))` -/
  | cons : (Γ : ECon) -> (Δ : ECon) -> (A : ETy) -> ESubst -> ETm -> ESubst
  deriving Repr, Inhabited
end

-- different "sizeOf", ignoring type indices.
mutual
  @[simp] def ECon.size : ECon -> Nat
  | .nil => 1
  | .ext Γ A => 1 + Γ.size + A.size

  @[simp] def ETy.size : ETy -> Nat
  | .U Δ => 1
  | .El Δ t => 1 + t.size
  | .Pi Δ A B => 1 + A.size + B.size

  @[simp] def EVar.size : EVar -> Nat
  | .vz .. => 0
  | .vs _ _ _ v => 1 + v.size

  @[simp] def ETm.size : ETm -> Nat
  | .var _ _ v => 1 + v.size
  | .app _ _ _ f a => 1 + f.size + a.size
  | .lam _ _ _ body => 1 + body.size
  | .error => 0

  @[simp] def ESubst.size : ESubst -> Nat
  | .nil .. => 1
  | .cons _ _ _ σ t => 1 + σ.size + t.size
end

/-- Look up the term stored in a substitution. -/
def substVarE : EVar -> ESubst -> ETm
| .vz _ _    , .cons _ _ _ _ t => t
| .vs _ _ _ v, .cons _ _ _ σ _ => substVarE v σ
| _, _ => .error

def ECon.len : ECon -> Nat
| .nil => 0
| .ext Γ A => 1 + Γ.len

def ESubst.len : ESubst -> Nat
| .nil _ => 0
| .cons _ _ _ σ _ => 1 + σ.len

/-- Notation: `Γ - n`. Drop the last `n` variables in the context.
  Example: `drop (Con.nil, A, B, C) 1 ≡ (Con.nil, A, B)`. -/
@[simp] def ECon.drop : (Γ : ECon) -> Fin (Γ.len + 1) -> ECon
| .nil    , n => .nil
| .ext Γ A, ⟨0  , h⟩ => Γ
| .ext Γ A, ⟨n+1, h⟩ => Γ.drop ⟨n, by rw [len] at h; linarith⟩

/-- Notation: `Γᵥ`. Get the type of the de-Brujin variable `v`.
   `get : (Γ : Con) -> (v : Fin Γ.len) -> Ty (drop Γ (v+1))`. -/
@[simp] def ECon.get : (Γ : ECon) -> (v : Fin Γ.len) -> ETy
| .nil    , v => Fin.elim0 v
| .ext Γ A, ⟨0  , h⟩ => A
| .ext Γ A, ⟨v+1, h⟩ => -- expected `Ty (drop (Γ, A) (v+1+1))`
  -- ! theorem drop_ext : drop (Γ, A) (v+1+1) = drop Γ (v+1)
  Γ.get ⟨v, by rw [len] at h; linarith⟩ -- : Ty (drop Γ (v+1))

@[aesop safe] theorem ECon.get_lt_con (Γ : ECon) (n : Fin Γ.len) : (Γ.get n).size < Γ.size := sorry
@[aesop safe] theorem ECon.len_le_sizeOf (Γ : ECon) : Γ.len <= Γ.size := sorry
@[aesop safe] theorem ESubst.len_le_sizeOf (σ : ESubst) : σ.len <= σ.size := sorry

def sum (lower upper : Nat) (f : Nat -> Nat) : Nat :=
  if lower <= upper then (f lower) + sum (lower + 1) upper f else 0
  termination_by 1 + upper - lower

/-- `(wknE Γ n).size`. Because `wkn (Con.nil, A, B, C) 1 ≡ (Subst.nil, Tm.var #2, Tm.var #1)`,
  so `1` for `Subst.nil`, and then for every term in the subst we have 1 for `Subst.cons`,
  1 for `Tm.var`, and `i` for de brujin `#i`. The `i` may not even be necessary actually,
  making the `sum` needless, but for now I've included `i` just in case. -/
def wknE.size (Γ : ECon) (n : Fin (Γ.len + 1)) : Nat := 1 + sum n.val (Γ.len - 1) (fun i => 2 + i)
-- theorem wknE_size (Γ : ECon) (n : Fin (Γ.len) + 1) : (wkn Γ n).size = wknE.size Γ n := sorry

mutual
  /-- `substTy {Γ Δ : Con} (A : Ty Δ) (σ : Γ <- Δ) : Ty Γ` -/
  def substTyE (Γ Δ : ECon) : ETy -> ESubst -> ETy
  | .U Δ, σ => .U Γ
  | .El Δ t, σ => .El Γ (substTmE Γ Δ t σ)
  | .Pi Δ A B, σ => -- Δ ⊢ A
    let Aσ : ETy /- Γ -/ := substTyE Γ Δ A σ -- `Γ ⊢ A[σ]`
    let wk_σ /- : (Γ, A[σ]) <- Δ -/ := comp (.ext Γ Aσ) Γ Δ σ (wkn (.ext Γ Aσ) 1) -- note that `wk σ = σ ∘ (wkn (Γ, A[σ]) 1)`
    let A_wk_σ : ETy := substTyE (.ext Γ Aσ) Δ A wk_σ -- `(Γ, A[σ]) ⊢ A[wk σ]`
    let vz : ETm /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ Aσ) A_wk_σ (.vz Γ Aσ) -- `.vz Γ A' : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = σ ∘ (wk id)`
    let δ : ESubst /- (Γ, A[σ]) <- (Δ, A) -/ := .cons (.ext Γ Aσ) Δ A (wk_σ) vz
    .Pi Γ Aσ (substTyE (.ext Γ Aσ) (.ext Δ A) B δ)
  termination_by A σ => Γ.size + A.size + σ.size

  /-- `substTm {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ (substTy A σ)` -/
  def substTmE (Γ Δ : ECon) : ETm -> ESubst -> ETm
  | .var _ _ v, σ => substVarE v σ -- just pick the term in the subst that v refers to. if ill-formed, then .error.
  | .app _Δ A B f a, σ => -- expected `Tm Γ B[id, a][σ]`
    let Aσ : ETy /- Γ -/ := substTyE Γ Δ A σ -- Γ ⊢ A[σ]
    -- let wk_σ : ESubst := wkE Γ Δ A' σ -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wk id)`
    let wk_σ : ESubst := comp (.ext Γ Aσ) Γ Δ σ (wkn (.ext Γ Aσ) 1) -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wkn (Γ, A[σ]) 1)`
    let A_wk_σ : ETy /- (Γ, A[σ]) -/ := substTyE (.ext Γ Aσ) Δ A wk_σ -- A[wk σ]
    let vz : ETm /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ Aσ) A_wk_σ (.vz Γ Aσ) -- `.vz Γ A[σ] : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = (wk id) ∘ σ`
    let δ : ESubst /- (Γ, A[σ]) <- (Δ, A) -/ := ESubst.cons (.ext Γ Aσ) Δ A (wk_σ) vz

    let B' : ETy := substTyE (.ext Γ Aσ) (.ext Δ A) B δ
    let f' : ETm := substTmE Γ Δ f σ -- `f[σ] : Tm Γ (Pi A B)[σ]`, where `(Pi A B)[σ] = Pi A[σ] B[wk σ, #0]` per definition of substTy
    let a' : ETm := substTmE Γ Δ a σ -- `a[σ] : Tm Γ A[σ]`
    let fa' : ETm := .app Γ Aσ B' f' a' -- `.app f[σ] a[σ] : Tm Γ B[wk σ, #0][id, a]`
    fa' -- ! here we need `((wk σ), #0) ∘ (id, a) = (id, a) ∘ σ` to typecheck.
  | .lam Δ A B body, σ => .error
  | .error, _ => .error
  termination_by t σ => Γ.size + t.size + σ.size

  /-- `wkn {Γ : Con} (n : Fin (Γ.len + 1)) : (Γ <- Γ - n)` -/
  def wkn (Γ : ECon) (n : Fin (Γ.len + 1)) : ESubst :=
    if h : Γ.len = n then .nil Γ
    else
      have h : n < Γ.len := sorry
      ESubst.cons Γ (Γ.drop n)
        (Γ.get ⟨n, by simp only [h]⟩) -- Γₙ
        (wkn Γ ⟨n+1, by linarith⟩) -- `wkn Γ (n+1) : Γ <- Γ - (n+1)`
        (.var Γ
          (substTyE Γ (Γ.drop (n+1)) (Γ.get ⟨n, by simp only [h]⟩) (wkn Γ ⟨n+1, by linarith⟩)) -- `Γᵥ[wki]`
          (mkVar Γ ⟨n, by linarith⟩)
        )
  termination_by Γ.size + (Γ.len - n) + wknE.size Γ n

  -- `mkVar : (Γ : Con) -> (v : Fin Γ.len) -> Var Γ (Γ.get v)[wkn Γ (v+1)]`
  def mkVar : (Γ : ECon) -> (v : Fin Γ.len) -> EVar
  | .nil, v => Fin.elim0 v
  | .ext Γ X, ⟨0  , _⟩ => -- expected `Var (Γ, X) (get (Γ, X) 0)[wkn (Γ, X) (0 + 1)]`
    -- by defeq we have `get (Γ, X) 0 ≡ X`
    .vz Γ X -- `: Var (Γ, X) X[wki]`, where `wki` is just a shorthand for `wkn (Γ, X) 1`.
  | .ext Γ X, ⟨v+1, h⟩ => -- expected `Var (Γ, X) (get (Γ, X) (v+1))[wkn (Γ, X) (v + 1 + 1)]`
    -- ! need theorem get_ext : get (Γ, X) (v+1) = get Γ v
    -- ! need theorem : wkn Γ (v+1) ∘ wkn (Γ, X) 1 = wkn (Γ, X) (v+1+1)
    .vs
      Γ
      (substTyE
        Γ
        (Γ.drop ⟨v+1, by rw [ECon.len] at h; linarith⟩)
        (Γ.get ⟨v, by rw [ECon.len] at h; linarith⟩) -- `Γᵥ`
        (wkn (.ext Γ X) ⟨v+1+1, by simp_all only [ECon.len, add_lt_add_iff_right]⟩) -- `wkn (Γ, X) (v+1+1)`
      ) -- `Γᵥ[wkn (Γ, X) (v+1+1)]`
      X
      (mkVar Γ ⟨v, by rw [ECon.len] at h; linarith⟩) -- `mkVar Γ v : Var Γ (Γ.get v)[wkn Γ (v+1)]`
  termination_by Γ v => Γ.size + v + wknE.size Γ ⟨v.val + 1, by simp_all only [add_lt_add_iff_right, Fin.is_lt]⟩

  /-- `comp {Γ Θ Δ : Con} : Subst Θ Δ -> Subst Γ Θ -> Subst Γ Δ` -/
  def comp (Γ Θ Δ : ECon) : ESubst -> ESubst -> ESubst
  | .nil Θ         , σ => .nil Γ
  | .cons Θ Δ A δ t, σ => -- `δ : Θ <- Δ`,   `σ : Γ <- Θ`,   `Θ ⊢ t : A[δ]`,   expected `Γ <- Δ, A`
    .cons Γ Δ A
      (comp Γ Θ Δ δ σ) -- δ ∘ σ : Γ <- Δ
      (substTmE Γ Θ t σ) -- `Γ ⊢ t[σ] : A[δ][σ]`, -- ! need theorem `A[δ][σ] = A[δ ∘ σ]`
  termination_by δ σ => σ.size + δ.size
end

#eval wkn (.nil) 0

/-- `id : {Γ : Con} -> (Γ <- Γ)` -/
def idE (Γ : ECon) : ESubst := wkn Γ 0

/-- `wki : {Γ : Con} -> {W : Ty Γ} -> (Γ, W <- Γ)` -/
def wkiE (Γ : ECon) (W : ETy) : ESubst := wkn (.ext Γ W) 1

/-- `wk : {Γ Δ : Con} -> {W : Ty Γ} -> (Γ <- Δ) -> (Γ, W <- Δ)` -/
def wkE (Γ Δ : ECon) (W : ETy) (σ : ESubst) : ESubst
  := comp (.ext Γ W) Γ Δ
      (wkiE Γ W) -- `wki : Γ,W <- Γ`
      σ

#eval idE .nil
#eval idE (.ext .nil (.U .nil))
#eval idE (.ext (.ext .nil (.U .nil)) (.U .nil))
#eval idE (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

def wk1 (Γ : ECon) : ESubst := wkn Γ 1
#eval wk1 (.ext .nil (.U .nil))
#eval wk1 (.ext (.ext .nil (.U .nil)) (.U .nil))
#eval wk1 (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

def wk2 (Γ : ECon) : ESubst := wkn Γ 2
#eval wk2 (.ext (.ext .nil (.U .nil)) (.U .nil))
#eval wk2 (.ext (.ext (.ext .nil (.U .nil)) (.U .nil)) (.U .nil))

/-- Parellel weakening `wkp {Γ Δ} {W : Ty Δ} (σ : Γ <- Δ) : (Γ, A[σ]) <- (Δ, A)`. This is the `δ` used in substTyE and substTmE. -/
def wkpE (Γ Δ : ECon) (W : ETy) (σ : ESubst) : ESubst := sorry -- TODO this is "just" `(wk σ, #0)`

-- # !
-- # Everything below this line is VERY out of date!

#exit

/-- `Subst (Γ, A) Γ`. This is usually two functions chained together: `wk id`, but we only need this version. -/
@[aesop unsafe]
def ESubst.wk (Γe : ECon) : ESubst := ESubst.weaken (ESubst.id Γe)

/-- `subst1 : Subst Γ (Γ, A) -/
@[aesop unsafe]
def ESubst.subst1 (Γe : ECon) (te : ETm) : ESubst := .cons (id Γe) te

-- #reduce ESubst.id (.ext (.ext .nil .U) .U)

mutual
  @[aesop safe constructors unsafe cases]
  inductive WCon : ECon -> Prop
  | nil : WCon .nil
  | ext : (Γw : WCon Γe) -> (Aw : WTy Γe Ae) -> WCon (ECon.ext Γe Ae)

  @[aesop safe constructors unsafe cases]
  inductive WTy : ECon -> ETy -> Prop
  | U : WTy Γe (.U Γe)
  | El : WTm Γe .U tE -> WTy Γe (.El tE)
  | Pi : (Aw : WTy Γe Ae) -> (Bw : WTy (.ext Γe Ae) Be) -> WTy Γe (.Pi Ae Be)
  /-- A mutual inductive type which may refer to existing types in Γ, and has type A. -/
  -- | mind : MInd /- Γ -/ A -> Ty Γ

  @[aesop safe constructors unsafe cases]
  inductive WVar : ECon -> ETy -> EVar -> Prop
  | vz : WVar (ECon.ext Γe Ae) (substTyE Ae (ESubst.wk Γe)) EVar.vz
  | vs : WVar Γe Ae ve -> WVar (ECon.ext Γe Be) (substTyE Ae (ESubst.wk Γe)) (EVar.vs ve)

  @[aesop safe constructors unsafe cases]
  inductive WTm : ECon -> ETy -> ETm -> Prop
  | var : WVar Γe Ae ve -> WTm Γe Ae (.var ve)
  | app {Ae Be : ETy} :
          {Aw : WTy Γe Ae} ->              -- A : Ty Γ
          {Bw : WTy (.ext Γe Ae) Be} ->    -- B : Ty (Γ, A)
          (fw : WTm Γe (.Pi Ae Be) fe) ->  -- f : Tm Γ (Pi A B)
          (aw : WTm Γe Ae ae) ->           -- a : Tm Γ A
          WTm Γe (substTyE Be (ESubst.subst1 Γe ae)) (.app fe ae) -- -> Tm Γ (B[Var.vz ↦ a] : Ty Γ) -- ! Without the subst, we'd have `Tm Γ (B : Ty (Γ, A))`, which is ill-typed.
  | lam : {Aw : WTy Γe Ae} ->
          {Bw : WTy (.ext Γe Ae) Be} ->
          (bodyw : WTm (.ext Γe Ae) Be bodye) ->
          WTm Γe (.Pi Ae Be) (.lam bodye)

  @[aesop safe constructors unsafe cases]
  inductive WSubst : ECon -> ECon -> ESubst -> Prop
  | nil : WSubst Γe Δe .nil
  | cons : WSubst Γe Δe δe -> WTm Γe (substTyE Ae δe) tE -> WSubst Γe (ECon.ext Δe Ae) (.cons δe tE)
end


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
