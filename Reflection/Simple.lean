-- Source: Chapter 2 of https://andraskovacs.github.io/pdfs/phdthesis_compact.pdf

/-
  # Types, Contexts, Variables in Contexts
-/

inductive Ty : Type
| nil   :               Ty
| self  :         Ty -> Ty
-- | other : (T : Type) ->  -> Ty
notation "⬝" => Ty.nil
notation "⬝" " ->> " A => Ty.self A

/-- Signature for one constructor.
  For example `TyA (⬝ ->> ⬝) Nat` reduces to `Nat -> Nat`. -/
def TyA : Ty -> Type -> Type
| ⬝      , X => X
| ⬝ ->> A, X => X -> TyA A X
#reduce TyA (⬝ ->> ⬝) Nat

def TyM : (A : Ty) -> {X Y : Type} -> (f : X -> Y) -> TyA A X -> TyA A Y -> Prop
|       ⬝, _, _, f, α₀, α₁ => f α₀ = α₁
| ⬝ ->> A, X, _, f, α₀, α₁ => (x : X) -> TyM A f (α₀ x) (α₁ (f x))

example : TyM         ⬝  (fun n => n      ) Nat.zero Nat.zero := by rfl
example : TyM         ⬝  (fun n => s!"{n}") Nat.zero "0" := by rewrite [TyM]; rfl
example : TyM (⬝ ->> ⬝) (fun n => n      ) Nat.succ Nat.succ := by
  rewrite [TyM]
  intro x
  rewrite [TyM]
  rfl
-- example : TyM (⬝ ->> ⬝) (fun n => s!"{n}") Nat.succ (fun n => /- parse n, incr, then toString again -/) := by done

/-- Displayed Algebra. -/
def TyD : (A : Ty) -> {X : Type} -> (motive : X -> Type) -> TyA A X -> Type
|       ⬝, _, motive, α => motive α
| ⬝ ->> A, X, motive, α => (x : X) -> (xD : motive x) -> TyD A motive (α x)

/-- Section. -/
def TyS : (A : Ty) -> {X : Type} -> {XD : X -> Type} -> (XS : (x : X) -> XD x) -> (α : TyA A X) -> TyD A XD α -> Prop
|       ⬝, _, _, XS, α, αD => XS α = αD
| ⬝ ->> A, X, _, XS, α, αD =>
  -- α  : TyA (⬝ ->> A) X    ===  (x : X) ->                TyA A X
  -- αD : TyD (⬝ ->> A) x α  ===  (x : X) -> (xD : XD x) -> TyD A XD (α x)
  (x : X) -> TyS A XS (α x) (αD x (XS x))


/-- Signature for an inductive type, i.e. list of ctor signatures.  Example:
```
def NatSig : Con := [⬝, ⬝ ->> ⬝]
``` -/
def Con := List Ty


/-- A variable refers to a context entry. Imagine that contexts are signatures for inductive types,
  then `Var.vz` refers to the first constructor of the inductive type. -/
inductive Var : Con -> Ty -> Type
| vz : Var (A :: Γ) A
| vs : Var Γ A -> Var (_ :: Γ) A

notation "vz" => Var.vz
notation "vsz" => Var.vs Var.vz
notation "vssz" => Var.vs (Var.vs Var.vz)

/-- This is essentially a tuple, but access occurs via the `Var`.  Example:
```
def NatConA : ConA NatSig Nat
| .(⬝)       , .vz     => Nat.zero
| .(⬝ ->> ⬝), .vs .vz => Nat.succ
``` -/
def ConA (Γ : Con) (X : Type) : Type
  := ⦃A : Ty⦄ -> Var Γ A -> TyA A X

-- ⦃a⦄
def NatSig : Con := [⬝, ⬝ ->> ⬝]
def NatConA : ConA NatSig Nat
| .(⬝)       , .vz     => Nat.zero
| .(⬝ ->> ⬝), .vs .vz => Nat.succ

def ConM (Γ : Con) {X Y : Type} (f : X -> Y) (γ₀ : ConA Γ X) (γ₁ : ConA Γ Y) : Prop
  := ⦃A : Ty⦄ -> (x : Var Γ A) -> TyM A f (γ₀ x) (γ₁ x)

example : ConM (X := Empty) [] (fun n => n) (fun o _ => nomatch o) (fun o _ => nomatch o) := by
  simp [ConM]
  intro A x
  exact nomatch x

example : ConM (X := Unit) (Y := Nat) [⬝] (fun u => 123) (fun | ⬝, .vz => ()) (fun | ⬝, .vz => nat_lit 123) := by
  simp only [ConM]
  intro A x
  cases A with
  | nil =>
    simp [TyM]
    let .vz := x
    sorry -- the goal here is essentially `123 = 123`, but Lean struggles with it.
  | self A' => exact nomatch x

/-- A context with natural numbers offset by one. -/
def NatConA_Add1 : ConA NatSig Nat
| .(⬝)       , .vz     => Nat.succ Nat.zero
| .(⬝ ->> ⬝), .vs .vz => Nat.succ

def NatConM_Add1 : ConM (X := Nat) (Y := Nat) [⬝, ⬝ ->> ⬝] (fun u => Nat.succ u) NatConA NatConA_Add1 := by
  intro A x
  match x with
  | .vz =>
    simp only [NatConA]
    rw [TyM]
    rfl
  | .vs .vz =>
    simp only [NatConA]
    rw [TyM]
    intro x
    rw [TyM]
    rw [NatConA_Add1]
    done

def ConD (Γ : Con) {X : Type} (XD : X -> Type) (γ : ConA Γ X) : Type
  := ⦃A : Ty⦄ -> (x : Var Γ A) -> TyD A XD (γ x)

def ConS (Γ : Con) {X : Type} {XD : X -> Type} (XS : (x : X) -> XD x) (γ₀ : ConA Γ X) (γ₁ : ConD Γ XD γ₀) : Prop
  := ⦃A : Ty⦄ -> (x : Var Γ A) -> TyS A XS (γ₀ x) (by rewrite [ConA, ConD] at *; exact γ₁ x) -- rw just for visualization




def Alg (Γ : Con) : Type 1
  := (X : Type) × ConA Γ X

/-- The (initial?) algebra of natural numbers. -/
def NatAlg : Alg NatSig := ⟨Nat, fun
  | ⬝, Var.vz => Nat.zero
  | ⬝ ->> ⬝, .vs .vz => Nat.succ⟩

def Mor : Alg Γ -> Alg Γ -> Type
| ⟨X₀, γ₀⟩, ⟨X₁, γ₁⟩ => (f : X₀ -> X₁) ×' ConM Γ f γ₀ γ₁


def DispAlg {Γ : Con} : Alg Γ -> Type 1
| ⟨X, γ⟩ => (XD : X -> Type) × ConD Γ XD γ

def Section {Γ : Con} : (alg : Alg Γ) -> DispAlg alg -> Type
| ⟨X, γ⟩, ⟨XD, γD⟩ => (XS : (x : X) -> XD x) ×' ConS Γ XS γ γD

/-- We can later obtain an inhabitant of `Inductive` by using `Ind`,
  see the examples at the end of this file. -/
def Inductive {Γ : Con} : Alg Γ -> Type 1
| γ => (γD : DispAlg γ) -> Section γ γD


/-
  # Terms, Substitutions
-/

inductive Tm : Con -> Ty -> Type
| var : Var Γ A -> Tm Γ A
| app : Tm Γ (⬝ ->> A) -> Tm Γ ⬝ -> Tm Γ A
notation t " @ " u => Tm.app t u
#check Tm.var .vz
#check Tm.app (Tm.var .vz) (Tm.var (.vs .vz))

def NaturalNumbers := Tm NatSig ⬝
def NaturalNumbers.zero : NaturalNumbers := Tm.var vz
def NaturalNumbers.one : NaturalNumbers := Tm.app (Tm.var vsz) (Tm.var vz)

/-- Interprets a term. -/
def TmA {A : Ty} : Tm Γ A -> {X : Type} -> ConA Γ X -> TyA A X
| .var x  , _, γ => γ x
| .app t u, _, γ =>
  -- let f   := TmA t γ
  -- let arg := TmA u γ
  -- f arg
  TmA t γ (TmA u γ)

example : TyA         ⬝  Nat := TmA (Tm.var      .vz ) NatConA -- Nat.zero
example : TyA (⬝ ->> ⬝) Nat := TmA (Tm.var (.vs .vz)) NatConA -- Nat.succ
example : TyA         ⬝  Nat := TmA (Tm.app (Tm.var (.vs .vz)) (Tm.var .vz)) NatConA -- Nat.succ Nat.zero
#reduce TmA (Tm.var .vz) NatConA
#reduce TmA (Tm.var (.vs .vz)) NatConA
#reduce TmA (Tm.app (Tm.var (.vs .vz)) (Tm.var .vz)) -- `#1 @ #0`
#reduce TmA (Tm.app (Tm.var (.vs .vz)) (Tm.var .vz)) NatConA

/-- For any term `t` -/
def TmM {X Y : Type} {γ₀ : ConA Γ X} {γ₁ : ConA Γ Y} {f : X -> Y} : (t : Tm Γ A) -> ConM Γ f γ₀ γ₁ -> TyM A f (TmA t γ₀) (TmA t γ₁) := by
  intro t γM
  induction t with
  | @var A x =>
    -- simp only [TmA]
    exact @γM A x
  | @app A t u ihₜ ihᵤ =>
    -- simp [TyM] at ihₜ
    -- simp [ConM] at γM
    have : f (TmA u γ₀) = TmA u γ₁ := ihᵤ
    have xxx := ihₜ (TmA u γ₀)
    have xxx' := this ▸ xxx
    exact xxx'

def TmD : (t : Tm Γ A) -> ConD Γ XD γ -> TyD A XD (TmA t γ)
| .var x  , γD => by
  simp [ConD] at γD
  have xxx := γD x
  exact xxx
| .app t u, γD => by
  simp [ConA] at γ
  simp [ConD] at γD
  exact TmD t @γD (TmA u γ) (TmD u γD)

def TmS : (t : Tm Γ A) -> ConS Γ XS γ γD -> TyS A XS (TmA t γ) (TmD t γD) := by
  intro t γS
  induction t with
  | @var A x => exact γS x
  | @app A t u ihₜ ihᵤ =>
    simp [TyS] at ihₜ
    have h : _ = _ := ihᵤ
    simp [TmD]
    exact h ▸ ihₜ (TmA u γ)
    done

/-- Substitutions replace variables (e.g. constructors, `Nat.succ`, `Nat.zero`, ...) with terms. -/
def Subst (Γ Δ : Con) : Type
  := ⦃A : Ty⦄ -> Var Δ A -> Tm Γ A

def subst : Tm Δ A -> Subst Γ Δ -> Tm Γ A
| .var x  , σ => σ x
| .app t u, σ => .app (subst t σ) (subst u σ)
notation:max t:100 "[" σ "]" => subst t σ

def Subst.id : Subst Γ Γ := fun _A => Tm.var

theorem subst_id (t : Tm Γ A) : t[Subst.id] = t := by
  induction t with
  | var x => simp only [subst, Subst.id]
  | app t u ihₜ ihᵤ => simp only [subst, ihₜ, ihᵤ]

/-- Composition of two substitutions. -/
def comp : Subst Δ Ω -> Subst Γ Δ -> Subst Γ Ω
| σ, δ, _, x => subst (σ x) δ

def SubA : Subst Γ Δ -> {X : Type} -> ConA Γ X -> ConA Δ X
| σ, _, γ, _, x => TmA (σ x) γ

def SubM {XM : X -> Y} : (σ : Subst Γ Δ) -> ConM Γ XM @γ₀ @γ₁ -> ConM Δ XM (SubA @σ @γ₀) (SubA @σ @γ₁)
| σ, γM, _, x => TmM (σ x) γM

def SubD : (σ : Subst Γ Δ) -> ConD Γ XD γ -> ConD Δ XD (SubA σ γ)
| σ, γD, _, x => TmD (σ x) γD

def SubS : (σ : Subst Γ Δ) -> ConS Γ XS γ γD -> ConS Δ XS (SubA σ γ) (SubD σ γD)
| σ, γS, _, x => TmS (σ x) γS

/-- This substitution does nothing. -/
example : Subst NatSig NatSig
| ⬝       , .vz     => Tm.var .vz
| ⬝ ->> ⬝, .vs .vz => Tm.var (.vs .vz)

#reduce TyA ⬝ (Tm [] ⬝)

def TyT : (A : Ty) -> Tm Ω A -> TyA A (Tm Ω ⬝)
| ⬝      , t => t
| ⬝ ->> A, t => fun u => TyT A (t @ u)

#reduce TyT ⬝ ?t
#reduce TyT ⬝ (.var .vz)
#reduce TyT (⬝ ->> ⬝) (.var .vz) (.var (.vs .vz))
#reduce TyT (Ω:=?Ω) (⬝ ->> ⬝) ?t
#reduce TyT (Ω:=?Ω) (⬝ ->> ⬝ ->> ⬝ ->> ⬝) ?t


def ConT : (Γ : Con) -> Subst Ω Γ -> ConA Γ (Tm Ω ⬝)
| _Γ, ν, A, x => TyT A (ν x)

-- t is a term in context Γ, and recall that Γ is a description of an inductive type such as Nat or String, etc.
-- And then applying a substitution ν to `t` and you obtain a term in context Ω, which describes a different
-- type, maybe even with a different amount of constructors.
-- For one of those constructors (described by A), we introduce a lambda for each of its arguments using `TyT`.
-- Then lhs of the eq is the "constructor" itself, in the process of being mapped from Γ to Ω.
-- Note that `ConT Γ ν` reduces to `TyT A (ν x)`, so we "pull in" the TyT under the TmA.
def TmT {A : Ty} : (t : Tm Γ A) -> (ν : Subst Ω Γ) -> TyT A (t[ν]) = TmA t (ConT Γ ν) := by
  intro t ν
  induction t with
  | var x =>
    -- simp [TmA]
    -- simp [ConT]
    -- rewrite [subst]
    rfl
  | app t u ihₜ ihᵤ =>
    rewrite [TmA]
    rewrite [<- ihₜ]
    rewrite [<- ihᵤ]
    rfl

def SubT : (σ : Subst Γ Δ) -> (ν : Subst Ω Γ) -> {A:Ty} -> (x : Var Δ A) -> ConT Δ (comp σ ν) x = SubA σ (ConT Γ ν) x
| σ, ν, _, x => TmT (σ x) ν

def TmAlg {Ω : Con} : Alg Ω
  := ⟨Tm Ω ⬝, ConT Ω Subst.id⟩




-- # Recursor and Eliminator construction

-- ## Recursor

variable {Ω : Con}
variable {X : Type}
variable (ω : ConA Ω X)

def R (ω : ConA Ω X) : Tm Ω ⬝ -> X
| t => TmA t ω

def TyR : (A : Ty) -> (t : Tm Ω A) -> TyM A (R ω) (TyT A t) (TmA t ω)
| ⬝      , t => by
  simp only [TyM]
  simp only [TyT]
  rfl
| ⬝ ->> A, t => by
  simp only [TyM]
  simp only [TyT]
  intro u
  simp only [R]
  let AR := TyR A (t @ u)
  exact AR

def ConR : (Γ : Con) -> (ν : Subst Ω Γ) -> ConM Γ (R ω) (ConT Γ ν) (SubA ν ω)
| _, ν, A, x => TyR ω A (ν x)

def Rec : (alg : Alg Ω) -> Mor TmAlg alg
| ⟨_X, ω⟩ => ⟨R ω, ConR ω Ω Subst.id⟩

def NatRec : Mor TmAlg NatAlg := Rec NatAlg


-- ## Eliminator

variable (XD : Tm Ω ⬝ -> Type)

/-- "Nothing happens if we evaluate a term with type `⬝` in the term model." -/
theorem nop (t : Tm Ω ⬝) : TmA t (ConT Ω Subst.id) = t := by
  simp only [<- TmT t Subst.id, subst_id t, TyT]

/-- The eliminator. -/
def E ⦃XD : Tm Ω ⬝ -> Type⦄ (ωD : ConD Ω XD (ConT Ω Subst.id)) (t : Tm Ω ⬝) : XD t
  := nop t ▸ TmD t ωD

-- set_option pp.explicit true in
set_option pp.proofs true in
def TyE : ⦃XD : Tm Ω ⬝ -> Type⦄ -> (ωD : ConD Ω XD (ConT Ω Subst.id)) -> (A : Ty) -> (t : Tm Ω A) -> TyS A (E ωD) (TmA t (ConT Ω Subst.id)) (TmD t ωD)
| XD, ωD, ⬝, t => by

  -- ! https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/rw.20term.20depended.20on.20by.20other.20argument/near/409268800
  have (a b : Tm Ω ⬝) (h : a = b) (d : TyD ⬝ (XD .) a)
    : TyS ⬝ (E ωD) a d = TyS ⬝ (E ωD) b (h ▸ d)
    := by subst h; rfl

  rw [this (TmA t (ConT Ω Subst.id)) t (nop t) (TmD t ωD)]
  rw [TyS]
  rewrite [E]
  rfl

| XD, ωD, ⬝ ->> A, t => by
  rw [TyS]
  intro u
  have ih := TyE ωD A (t @ u)
  simp only [TmD] at ih
  simp only [TmA] at ih
  -- have xd (u) : TyD ⬝ XD (TmA u (ConT Ω Subst.id)) = XD u := by simp only [TyD, nop]
  have (fu u) (h : fu = u) (d) :
      TyS A (E ωD) (TmA t (ConT Ω Subst.id) fu) (TmD t ωD fu d)
    = TyS A (E ωD) (TmA t (ConT Ω Subst.id)  u) (TmD t ωD  u (h ▸ d))
    := by subst h; rfl
  rw [this (TmA u (ConT Ω Subst.id)) u (nop u)] at ih
  simp [E]
  exact ih

def ConE : (Γ : Con) -> (ν : Subst Ω Γ) -> ConS Γ (E ωD) (SubA ν (ConT Ω Subst.id)) (SubD ν ωD)
| _, ν, A, x => TyE ωD A (ν x)

-- set_option linter.unusedVariables false in
def Ind : (alg : DispAlg (@TmAlg Ω)) -> Section TmAlg alg
| ⟨_XD, ωD⟩ => ⟨E ωD, ConE Ω Subst.id⟩ -- XD is used implicitly





/-
  ## Example time!
  So, ... can we do some arithmetic with what we have so far?
  We have natural numbers, we should be able to define addition.
  We can also define booleans and some simple connectives.
  As a guiding example we have the following `IsEven` function which maps from `Nat` to `Bool`.
-/

/-- IsEven without using any signatures. -/
def NatIsEven_boring : Nat -> Bool
| 0          => true
| Nat.succ n => not (NatIsEven_boring n)


namespace Example.NoTA
/-
  ### Without using Term Algebras
-/

  /-- The recursor `Nat.rec` generated by Lean is compatible with our `Inductive` demands.
    This operates on Lean terms, i.e. you can put an actual `Nat.succ Nat.zero` into it.
    I left much redundant stuff in this def to hopefully explain its inner workings.
    -/
  noncomputable def NatInd : Inductive (Γ := NatSig) NatAlg := by
    intro ⟨XD, d⟩
    -- let xxx : TyD         ⬝  XD Nat.zero := d (.vz) -- : XD 0
    -- let yyy : TyD (⬝ ->> ⬝) XD Nat.succ := d (.vs .vz) -- : (x : Nat) → XD x → XD (Nat.succ x)
    -- simp only [Inductive, Section]
    let XS : (t : Nat) → XD t := @Nat.rec XD (d .vz) (d (.vs .vz))
    let zero_S :              XS   Nat.zero   = d .vz                :=          Eq.refl _
    let succ_S : (n : Nat) -> XS (Nat.succ n) = d (.vs .vz) n (XS n) := fun n => Eq.refl _
    -- simp only [NatAlg, NatSig]
    exact ⟨XS, fun | ⬝, .vz => zero_S | ⬝ ->> ⬝, .vs .vz => succ_S⟩

  /-- `IsEven` using Lean's recursor, but constrained by `Section`. -/
  noncomputable def NatIsEven /- : Section NatAlg _ -/ := NatInd ⟨fun _ => Bool, fun
  | ⬝, .vz => true
  | ⬝ ->> ⬝, .vs .vz => fun _n ihₙ => not ihₙ⟩

  -- It reduces properly! Remember `NatIsEven.fst` is the recursor,
  -- and `NatIsEven.snd` are the reduction rules (iotas), which I guess are instantiated for IsEven.
  example : NatIsEven.fst 22 = true := by rfl
  example : NatIsEven.fst 33 = false := by rfl
  example : NatIsEven.fst .zero = true := NatIsEven.snd .vz
  example : ∀n, NatIsEven.fst (.succ n) = not (NatIsEven.fst n) := NatIsEven.snd (.vs .vz)

end Example.NoTA

namespace Example.TA1
/-
  ### Using Term Algebras (only Nat)
  We still use Lean's `Bool`.
-/

  def NatAlg' : Alg NatSig := ⟨Tm NatSig ⬝, fun
  |        ⬝,     .vz =>           Tm.var      .vz
  | ⬝ ->> ⬝, .vs .vz => fun n => (Tm.var (.vs .vz)) @ n⟩

  /-- Term algebra with only natural numbers.
    Note how `NatAlg` nor `Nat` doesn't actually occur here! Even `NatSig` is just `[⬝, ⬝ ->> ⬝]`. -/
  def NatAlg : Alg NatSig := ⟨Tm NatSig ⬝, ConT NatSig Subst.id⟩

  def NatInd : Inductive (Γ := NatSig) NatAlg := Ind

  def NatIsEven := NatInd ⟨fun (_ : Tm NatSig ⬝) => Bool, fun
  |        ⬝,     .vz => true
  | ⬝ ->> ⬝, .vs .vz => fun _n ihₙ => not ihₙ⟩

end Example.TA1

namespace Example.TA2
/-
  ### Using two interacting Term Algebras (Nat, Bool)
  We now have no mention of Lean's `Nat` or `Bool`, everything happens entirely within our new theory.
  I duplicated `NatSig` etc to make this a pretty, self-contained example.
-/

  /-- `[Nat.zero, Nat.succ]` -/
  def NatSig := [⬝, ⬝ ->> ⬝]
  /-- `⟨Nat.rec, iotas...⟩` -/
  def NatInd : Inductive ⟨Tm NatSig ⬝, ConT NatSig Subst.id⟩ := Ind

  /-- `[false, true]` -/
  def BoolSig := [⬝, ⬝]
  /-- `⟨Bool.rec, iotas...⟩` -/
  def BoolInd : Inductive ⟨Tm BoolSig ⬝, ConT BoolSig Subst.id⟩ := Ind

  /-- `not` implemented using own own derived recursor, entirely on term algebras!
    We also get reduction rules from `BoolInd`, but we don't need them, hence the `|>.fst`. -/
  def BoolNot : Tm BoolSig ⬝ -> Tm BoolSig ⬝ :=
    BoolInd ⟨fun _ => Tm BoolSig ⬝, fun
      | ⬝,     .vz => Tm.var (.vs .vz) -- | false => true
      | ⬝, .vs .vz => Tm.var (    .vz) -- | true => false
    ⟩ |>.fst

  -- It reduces!
  #reduce BoolNot (Tm.var .vz) -- not false = true
  #reduce BoolNot (Tm.var (.vs .vz)) -- not true = false
  example : BoolNot (Tm.var .vz) = (Tm.var (.vs .vz)) := by rfl

  def IsEven : Tm NatSig ⬝ -> Tm BoolSig ⬝ :=
    NatInd ⟨fun (_ : Tm NatSig ⬝) => Tm BoolSig ⬝, fun
      |        ⬝,     .vz => Tm.var (.vs .vz) -- 0 => true
      | ⬝ ->> ⬝, .vs .vz => fun _n (ihₙ : Tm BoolSig ⬝) => BoolNot ihₙ -- n + 1 => !(isEven n)
    ⟩ |>.fst

  -- Some convenience functions to type less
  def fals : Tm BoolSig ⬝ := Tm.var (    .vz)
  def tru  : Tm BoolSig ⬝ := Tm.var (.vs .vz)
  def nat0 : Tm NatSig ⬝ := Tm.var .vz
  def natS : Tm NatSig (⬝ ->> ⬝) := Tm.var (.vs .vz)

  def nat : Nat -> Tm NatSig ⬝
  | 0 => nat0
  | .succ n => natS @ (nat n)
  -- this would have also worked:
  -- | .succ n => (nat n)[fun | ⬝, .vz => natS @ nat0 | ⬝ ->> ⬝, .vs .vz => .var (.vs .vz)]

  def tan : Tm NatSig ⬝ -> Nat
  | Tm.var .vz => 0
  | Tm.app _s z => Nat.succ (tan z)

  theorem tan_nat_inverse : tan (nat n) = n := by induction n with
  | zero => simp
  | succ n ih => simp [tan, nat, ih]

  #reduce nat 0
  #reduce nat 1
  #reduce nat 2
  #reduce nat 3

  #reduce IsEven ((.var vz)) -- true
  #reduce IsEven (nat 10)
  #reduce IsEven (nat 3)

end Example.TA2
