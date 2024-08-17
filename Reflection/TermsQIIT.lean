import Aesop
import Reflection.Util.Vec

set_option linter.unusedVariables false
set_option pp.fieldNotation.generalized false

mutual
  @[aesop unsafe constructors cases]
  inductive ECon : Type
  | nil : ECon
  | ext : ECon -> ETy -> ECon
  deriving Repr

  /-- `Ty : Con -> Type` -/
  @[aesop unsafe constructors cases]
  inductive ETy : Type
  /-- `U Γ : Ty Γ` -/
  | U : ECon -> ETy
  /-- `El {Γ} : (t : Tm Γ U) -> Ty Γ` -/
  | El : ECon -> ETm -> ETy
  /-- `Pi {Γ} : (A : Ty Γ) -> (B : Ty (ext Γ A)) -> Ty Γ` -/
  | Pi : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> ETy
  -- | substTy : ETy -> ESubst -> ETy
  deriving Repr

  /-- `Var : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop unsafe constructors cases]
  inductive EVar : Type
  /-- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wk id]`, note that `wk id : (Γ, A) <- Γ`, thus `Γ, A ⊢ A[wk id]` -/
  | vz : (Γ : ECon) -> (A : ETy) -> EVar
  /-- `vs {Γ} {A B : Ty Γ} : Var Γ A -> Var (Γ, B) (substTy A wk)` -/
  | vs : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> EVar -> EVar
  deriving Repr

  /-- `Tm : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop unsafe constructors cases]
  inductive ETm : Type
  /-- `var {Γ} {A : Ty Γ} : Var Γ A -> Tm Γ A` -/
  | var : (Γ : ECon) -> (A : ETy) -> EVar -> ETm
  -- /-- `app {Γ} : {A : Ty Γ} -> {B : Ty (ext Γ A)} -> (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[Var.vz ↦ a]`, here note that `Var.vz ↦ a` can be written as `Subst.cons Subst.id a`. -/
  /-- `app {Γ} : {A : Ty Γ} -> {B : Ty (ext Γ A)} -> (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[id, a]` -/
  | app : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> (f : ETm) -> (a : ETm) -> ETm
  /-- `lam {Γ} : {A : Ty Γ} -> {B : Ty (ext Γ A)} -> (body : Tm (ext Γ A) B) -> Tm Γ (Pi A B)` -/
  | lam : (Γ : ECon) -> (A : ETy) -> (B : ETy) -> (body : ETm) -> ETm
  /-- necessary because of substVarE. Will be proven impossible in the final IIRT. -/
  | error : ETm
  deriving Repr

  @[aesop unsafe constructors cases]
  inductive ESubst : Type
  /-- `Subst.nil : Subst Γ Con.nil` -/
  | nil : (Γ : ECon) -> ESubst
  /-- `cons : (δ : Subst Γ Δ) -> (t : Tm Γ (substTy A δ)) -> Subst Γ (Δ, A)` -/
  | cons : (Γ : ECon) -> (Δ : ECon) -> (A : ETy) -> ESubst -> ETm -> ESubst
  deriving Repr
end

mutual
  /-- Look up the term stored in a substitution. -/
  def substVarE : EVar -> ESubst -> ETm
  | .vz _ _    , .cons _ _ _ _ t => t
  | .vs _ _ _ v, .cons _ _ _ σ _ => substVarE v σ
  | _, _ => .error
  termination_by v _ => sizeOf v

  /-- `substTy {Γ Δ : Con} (A : Ty Δ) (σ : Subst Γ Δ) : Ty Γ` -/
  def substTyE (Γ Δ : ECon) : ETy -> ESubst -> ETy
  | .U Δ, σ => .U Γ
  | .El Δ t, σ => .El Γ (substTmE Γ Δ t σ)
  | .Pi Δ A B, σ => -- Δ ⊢ A
    let A' : ETy /- Γ -/ := substTyE Γ Δ A σ -- Γ ⊢ A[σ]
    let wk_σ : ESubst := wkE Γ Δ A' σ -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wk id)`
    let A'' : ETy := substTyE (.ext Γ A') Δ A wk_σ -- `A[wk σ] : (Γ, A[σ])`
    let vz : ETm /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ A') A'' (.vz Γ A') -- `.vz Γ A' : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = σ ∘ (wk id)`
    let δ : ESubst /- (Γ, A[σ]) <- (Δ, A) -/ := ESubst.cons (.ext Γ A') Δ A (wk_σ) vz
    .Pi Γ A' (substTyE (.ext Γ A') (.ext Δ A) B δ)
  termination_by A σ => sizeOf A + sizeOf σ

  /-- `substTm {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ (substTy A σ)` -/
  def substTmE (Γ Δ : ECon) : ETm -> ESubst -> ETm
  | .var _ _ v, σ => substVarE v σ -- just pick the term in the subst that v refers to. if ill-formed, then.... uh... welp.
  | .app _Δ A B f a, σ => -- expected `Tm Γ B[id, a][σ]`
    let A' : ETy /- Γ -/ := substTyE Γ Δ A σ -- Γ ⊢ A[σ]
    let wk_σ : ESubst := wkE Γ Δ A' σ -- `wk σ : (Γ, A[σ]) <- Δ`, note that `wk σ = σ ∘ (wk id)`
    let A'' : ETy /- (Γ, A[σ]) -/ := substTyE (.ext Γ A') Δ A wk_σ
    let vz : ETm /- (Γ, A[σ]) A[wk σ] -/ := .var (.ext Γ A') A'' (.vz Γ A') -- `.vz Γ A' : Var (Γ, A[σ]) A[σ][wk id]`, note that `wk σ = σ ∘ (wk id)`
    let δ : ESubst /- (Γ, A[σ]) <- (Δ, A) -/ := ESubst.cons (.ext Γ A') Δ A (wk_σ) vz

    let B' : ETy := substTyE (.ext Γ A') (.ext Δ A) B δ
    let f' : ETm := substTmE Γ Δ f σ -- `f[σ] : Tm Γ (Pi A B)[σ]`, where `(Pi A B)[σ] = Pi A[σ] B[wk σ, #0]` per definition of substTy
    let a' : ETm := substTmE Γ Δ a σ -- `a[σ] : Tm Γ A[σ]`
    let fa' : ETm := .app Γ A' B' f' a' -- `.app f[σ] a[σ] : Tm Γ B[wk σ, #0][id, a]`
    fa' -- ! here we need `((wk σ), #0) ∘ (id, a) = (id, a) ∘ σ` to typecheck.
  | .lam Δ A B body, σ => sorry
  | .error, _ => .error
  termination_by t σ => sizeOf t + sizeOf σ

  /-- `wk {Γ Δ : Con} {W : Ty Γ} : Subst Γ Δ -> Subst (Γ, W) Δ` -/
  def wkE (Γ _Δ : ECon) (W : ETy) : ESubst -> ESubst
  | .nil Δ => .nil (.ext Γ W)
  | .cons _ Δ A σ a => -- A : Ty Δ,   σ : Γ <- Δ,   a : Tm Γ A[σ],    expecting (Γ, W) <- (Δ, A)
    let wk_σ := wkE Γ Δ W σ -- `wk σ : (Γ, W) <- Δ`
    let A_wk_σ := substTyE (.ext Γ W) Δ A wk_σ -- `A[wk σ] : Ty (Γ, W)`
    let a' : ETm := substTmE Γ (.ext Γ W) a (wkE Γ Γ W (idE Γ)) -- `a[wk id] : Tm (Γ, W) A[σ][wk id]`
    let δ : ETm -> ESubst := .cons (.ext Γ W) Δ A wk_σ -- `δ : Tm (Γ, W) A[wk σ] -> ((Γ, W) <- (Δ, A))`
    δ a' -- ! We use `σ ∘ (wk id) = wk σ` here (at the `a'`)
  termination_by σ => sizeOf σ

  /-- `id {Γ : Con} : Subst Γ Γ` -/
  def idE : (Γ : ECon) -> ESubst
  | .nil => .nil .nil -- `Subst .nil .nil`
  | .ext Γ A => -- expecting `(Γ, A) <- (Γ, A)`
    let wk1 := wkE Γ Γ A (idE Γ) -- `wk1 : (Γ, A) <- Γ`
    .cons (.ext Γ A) Γ A -- `cons (Γ, A) Γ A : (δ : (Γ, A) <- Γ) -> (t : Tm (Γ, A) A[δ]) -> ((Γ, A) <- (Γ, A))`
      wk1 -- `cons (Γ, A) Γ A wk1 : (t : Tm (Γ, A) A[wk]) -> Subst (Γ, A) (Γ, A)`
      (.var (.ext Γ A) (substTyE (.ext Γ A) Γ A wk1) (.vz Γ A))
  termination_by Γ => sizeOf Γ
end

#exit
-- #exit

mutual
  /-- Increments all de brujin variables except the variable 0. -/
  def weaken_skip_1 (X : ETy /- Γ -/): ETy /- (Γ, A) -/ -> ETy /- (Γ, X, A[wk]) -/ := fun _ => .El .nil .error -- HACKY

  /-- `vshift {Γ : Con} {A X : Ty Γ} : Tm Γ A -> Tm (Γ, X) (substTy A wk)` -/
  def vshiftE (X : ETy) : (t : ETm) -> ETm
  | (ETm.var Γ A v) => -- `v : Var Γ A`   ⊢   `Tm (Γ, X) (substTy A wk)`
    -- have : sizeOf Γ < sizeOf X := sorry
    -- have : sizeOf X < sizeOf (ETm.var Γ A v) := sorry
    -- let idΓ := idE Γ
    let ΓX := ECon.ext Γ X
    .var (.ext Γ X)
      -- `.var (Γ, X) : (A : Ty (Γ, X)) -> Var (Γ, X) A -> Tm (Γ, X) A`

      -- (substTyE A (weakenE X (idE Γ))) -- `weaken Subst.id : Subst (Γ, X) Γ`    `substTyE A wk : Ty (Γ, X)`
      (substTyE A (weakenE X (idE Γ))) -- `weaken Subst.id : Subst (Γ, X) Γ`    `substTyE A wk : Ty (Γ, X)`

      -- `.var (Γ, X) (substTy A wk) : Var (Γ, X) (substTy A wk) -> Tm (Γ, X) (substTy A wk)`
      (.vs Γ A X -- `.vs Γ A X : Var Γ A -> Var (Γ, X) (substTy A wk)`
        v
      )
  -- Reminder: `Tm.app {Γ} : {A : Ty Γ} -> {B : Ty (Γ, A)} -> (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[Var.vz ↦ a]`
  | .app Γ A B f a => -- Have   `A : Ty Γ`    `B : Ty (Γ, A)`   `f : Tm Γ (Pi A B)`    `a : Tm Γ A`     expecting `Tm (Γ, X) B[a][wk]`, note that `B[a] : Ty Γ`, and then `B[a][wk] : Ty (Γ, X)`
    .app (.ext Γ X) -- `app (Γ, X) : (A : Ty (Γ, X)) -> {B : Ty (Γ, X, A)} -> (f : Tm (Γ, X) (Pi A B)) -> (a : Tm (Γ, X) A) -> Tm (Γ, X) B[Var.vz ↦ a]`
      (substTyE A (weakenE A (idE Γ))) -- this argument is `A[wk]`
      -- `app (Γ, X) A[wk] : {B : Ty (Γ, X, A[wk])} -> (f : Tm (Γ, X) (Pi A[wk] B)) -> (a : Tm (Γ, X) A[wk]) -> Tm (Γ, X) B[Var.vz ↦ a]`
      -- ! Now the problem is that we have `B : Ty (Γ, A)`, but we expect `Ty (Γ, X, A[wk])`. Fortunately we know that `A` doesn't depend on `X`, so we can reorder it.
      -- ! ...but how.
      (weaken_skip_1 X B) -- just assume such a function can be implemented
      -- `app (Γ, X) A[wk] (derp X B) : (f : Tm (Γ, X) (Pi A[wk] (derp X B))) -> (a : Tm (Γ, X) A[wk]) -> Tm (Γ, X) (derp X B)[Var.vz ↦ a]`
      (vshiftE X f) -- `vshift f : Tm (Γ, X) (Pi A B)[wk]` -- ! Need (β?)-theorem: `(Pi A B)[wk] = Pi A[wk] (derp X B)`, then cast this arg with it
      -- `app (Γ, X) A[wk] (derp X B) (vshift f) : (a : Tm (Γ, X) A[wk]) -> Tm (Γ, X) (derp X B)[Var.vz ↦ a]`
      (vshiftE X a) -- `vshift a : Tm (Γ, X) A[wk]`
      -- `app (Γ, X) A[wk] (derp X B) (vshift f) (vshift a) : Tm (Γ, X) (derp X B)[Var.vz ↦ a]`
  | .lam Γ A B body => .error
    -- .lam (.ext Γ B) A B (vshiftE body)
  | .error => .error
  termination_by t => sizeOf X + sizeOf t

  /-- `weaken : Subst Γ Δ -> Subst (Γ, X) Δ` -/
  def weakenE (X : ETy) : ESubst -> ESubst
  | .nil Γ => .nil (.ext Γ X)
  | .cons Γ Δ A σ t => .cons (.ext Γ X) Δ X
    (weakenE X σ) -- `σ : Subst Γ Δ`     `weaken σ : Subst (Γ, X) Δ`
    (vshiftE X t) -- `t : Tm Γ A`     `vshift t : Tm (Γ, X) A[wk]`
  termination_by σ => sizeOf σ

  /-- `Subst Γ Γ` -/
  def idE : (Γ : ECon) -> ESubst
  | .nil => .nil .nil -- `Subst .nil .nil`
  | .ext Γ A => -- ⊢ `Subst (Γ, A) (Γ, A)`
    -- `cons : (Γ Δ : Con) -> (A : Ty Δ) -> (δ : Subst Γ Δ) -> (t : Tm Γ A[δ]) -> Subst Γ (Δ, A)`
    .cons (.ext Γ A) Γ A
      -- `cons (Γ, A) Γ A : (δ : Subst (Γ, A) Γ) -> (t : Tm (Γ, A) A[δ]) -> Subst (Γ, A) (Γ, A)`
      (weakenE A (idE Γ))
      -- `cons (Γ, A) Γ A wk : (t : Tm (Γ, A) A[wk]) -> Subst (Γ, A) (Γ, A)`
      (.var Γ A (.vz Γ A))
  termination_by Γ => sizeOf Γ

  -- def wkE (Γ : ECon) (A : ETy) : ESubst := weakenE A (idE Γ)
  -- termination_by 1 + sizeOf Γ
end

#reduce idE .nil
#eval idE (.ext .nil (.U .nil))
#check weakenE


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
