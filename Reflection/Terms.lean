import Aesop
set_option linter.unusedVariables false
set_option pp.fieldNotation.generalized false

open Aesop

/- # The original IIRT
mutual
  inductive Con : Type
  | nil : Con
  | ext : (Γ : Con) -> (A : Ty Γ) -> Con

  inductive Ty : Con -> Type
  | U : Ty Γ
  | El : Tm Γ U -> Ty Γ
  | Pi : (A : Ty Γ) -> (B : Ty (ext Γ A)) -> Ty Γ
  /-- A mutual inductive type which may refer to existing types in Γ, and has type A. -/
  | mind : MInd /- Γ -/ A -> Ty Γ

  inductive Tm : (Γ : Con) -> Ty Γ -> Type
  | var : Var Γ A -> Tm Γ A
  | app : {A : Ty Γ} ->
          {B : Ty (ext Γ A)} ->
          (f : Tm Γ (Pi A B)) ->
          (a : Tm Γ A) ->
          Tm Γ B[Var.vz ↦ a]
  | lam : {A : Ty Γ} ->
          {B : Ty (ext Γ A)} ->
          (body : Tm (ext Γ A) B) ->
          Tm Γ (Pi A B)

  inductive Subst : (Γ : Con) -> (Δ : Con) -> Type
  | nil : Subst Γ .nil
  | cons : (δ : Subst Γ Δ) -> Tm Γ (substTy δ A) -> Subst Γ (Δ, A)

  def substTy {Γ Δ : Con} : Ty Δ -> Subst Γ Δ -> Ty Γ
  | U, σ => U
  | El Self, σ => El (substTm Self σ)
  | Pi A B, σ => ???
  | mind, σ => ???

  def substTm {Γ Δ : Con} : Tm Δ A -> (σ : Subst Γ Δ) -> Tm Γ A[σ]
  | var v, σ => substVar v σ
  | app f a, σ => app (substTm f σ) ?a
  | lam body, σ => ???
end
-/

-- /-- A mutual inductive type. -/
-- structure MInd /- (Γ : Tele) -/ (A : Tyₛ /- Γ -/) where
--   Ωₛ : Conₛ /- Γ -/
--   Ωₚ : Conₚ Ωₛ /- Γ -/
--   T : Tmₛ Ωₛ A

mutual
  @[aesop unsafe constructors cases]
  inductive ECon : Type
  | nil : ECon
  | ext : ECon -> ETy -> ECon

  @[aesop unsafe constructors cases]
  inductive ETy : Type
  | U : ETy
  | El : ETm -> ETy
  | Pi : ETy -> ETy -> ETy

  @[aesop unsafe constructors cases]
  inductive EVar : Type
  | vz : EVar
  | vs : EVar -> EVar

  @[aesop unsafe constructors cases]
  inductive ETm : Type
  | var : EVar -> ETm
  | app : (f : ETm) -> (a : ETm) -> ETm
  | lam : (body : ETm) -> ETm
  /-- necessary because of substVarE. Will be proven impossible in the final IIRT. -/
  | error : ETm

  @[aesop unsafe constructors cases]
  inductive ESubst : Type
  | nil : ESubst
  | cons : ESubst -> ETm -> ESubst
end

@[aesop unsafe]
def substVarE : EVar -> ESubst -> ETm
| .vz, .cons _ t => t
| .vs v, .cons σ _ => substVarE v σ
| _, _ => .error

@[aesop unsafe]
def substTmE : ETm -> ESubst -> ETm
| .var v, σ => substVarE v σ -- just pick the term in the subst that v refers to. if ill-formed, then.... uh... welp.
| .app f a, σ => .app (substTmE f σ) (substTmE a σ)
| .lam body, σ => .lam (substTmE body σ)
| .error, _ => .error

@[aesop unsafe]
def substTyE : ETy -> ESubst -> ETy
| .U, σ => .U
| .El t, σ => .El (substTmE t σ)
| .Pi A B, σ => .Pi (substTyE A σ) (substTyE B σ) -- not sure about the `substTyE B σ` here.


/-- `Tm Γ A -> Tm (Γ, B) A` -/
@[aesop unsafe]
def ESubst.vshift : ETm -> ETm
| .var v => .var (.vs v)
| .app f a => .app (vshift f) (vshift a)
| .lam body => .lam (vshift body)
| .error => .error

/-- `Subst Γ Δ -> Subst (Γ, A) Δ` -/
@[aesop unsafe]
def ESubst.weaken : ESubst -> ESubst
| .nil => .nil
| .cons σ t => .cons (weaken σ) (vshift t)

/-- `Subst Γ Γ` -/
@[aesop unsafe]
def ESubst.id : ECon -> ESubst
| .nil => .nil
| .ext Γ A => .cons (weaken (id Γ)) (.var .vz)

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
  | U : WTy Γe .U
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
def WSubst.weaken (Γw : WCon Γe) (Δw : WCon Δe) (Aw : WTy Γe Ae) : (σw : WSubst Γe Δe σe) -> WSubst (.ext Γe Ae) Δe (ESubst.weaken σe) := sorry

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
    have : B_subst_a = B
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
