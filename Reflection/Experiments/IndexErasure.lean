import Reflection.MutualInductive

open Tyₛ Tyₚ Varₛ Varₚ

-- # Erasure

def ETyₛ : Tyₛ.{u} -> Tyₛ.{u}
| _ => U

/-- For example maps sort-ctx `[Vec : Nat -> U, ...]` into `[VecE : U, ...]`. -/
def EConₛ : Conₛ.{u} -> Conₛ.{u}
| ⬝      => ⬝
| Γₛ ▹ _ => EConₛ Γₛ ▹ U

/-- This is a no-op, other than changing the type of the variable. -/
def EVarₛ : Varₛ Γₛ Aₛ -> Varₛ (EConₛ Γₛ) U
| .vz   => .vz
| .vs v => .vs (EVarₛ v)

/-- For example maps `Vec : Nat -> U ⊢ Vec 123 : U` into `VecE : U ⊢ VecE : U`. -/
def ETmₛ : Tmₛ Γₛ Aₛ -> Tmₛ (EConₛ Γₛ) U
| .var v              => .var (EVarₛ v)
| .app (A := _Aₛ) t u => ETmₛ t

/-- For example for `Vec.nil`, maps `Vec : Nat -> U ⊢ Vec 0` into `VecE : U ⊢ VecE`,
and for `Vec.cons` maps `Vec : Nat -> U ⊢ (n:Nat) -> α -> Vec n -> Vec (n+1)`
into `VecE : U ⊢ (n:Nat) -> α -> VecE -> VecE`. -/
def ETyₚ {Γₛ : Conₛ} : Tyₚ Γₛ -> Tyₚ (EConₛ Γₛ)
| El         Self => El (ETmₛ Self)
| PPi   T    Rest => PPi T (fun t => ETyₚ (Rest t))
| PFunc Self Rest => PFunc (ETmₛ Self) (ETyₚ Rest)

def EConₚ : Conₚ Γₛ -> Conₚ (EConₛ Γₛ)
| ⬝ => ⬝
| Γ ▹ A => (EConₚ Γ) ▹ (ETyₚ A)

def EVarₚ : Varₚ Γ A -> Varₚ (EConₚ Γ) (ETyₚ A)
| .vz => .vz
| .vs v => .vs (EVarₚ v)

def ETmₚ : Tmₚ Γ A -> Tmₚ (EConₚ Γ) (ETyₚ A)
| .var v => .var (EVarₚ v)
| .app (A := _A) t u => .app (ETmₚ t) u
| .appr t u => .appr (ETmₚ t) (ETmₚ u)

-- # Guard

/-- For example maps `Vec : Nat -> U` to `VecG : Nat -> VecE -> U`.
  Note that `∀Aₛ, TyₛA (eraseTyₛ Aₛ) = Type`. -/
-- def guardTyₛ : (Aₛ : Tyₛ.{u}) -> TyₛA.{u, u} (eraseTyₛ Aₛ) -> Tyₛ.{u}
def GTyₛ : (Aₛ : Tyₛ.{u}) -> Type u -> Tyₛ.{u}
| U         , aₛE => SPi aₛE (fun _ => U)
| SPi T Rest, aₛE => SPi T   (fun t => GTyₛ (Rest t) aₛE)

/-- For example maps sort-stx `[Vec : Nat -> U]` into `[VecG : Nat -> VecE -> U]`. -/
def GConₛ.{u} : (Γₛ : Conₛ.{u}) -> (γₛE : ConₛA.{u, u} (EConₛ Γₛ)) -> Conₛ.{u}
| ⬝      , ⟨⟩         => ⬝
| Γₛ ▹ Aₛ, ⟨γₛE, aₛE⟩ => Conₛ.ext (GConₛ Γₛ γₛE) (GTyₛ Aₛ aₛE)

/-- Given a variable `Vec:N->U ⊢ VAR(Vec) : N->U`, we return `VecG:N->VecE->U ⊢ VAR(VecG) : N->VecE->U`.
  The runtime de-brujin value of this variable doesn't change. So this is basically just a cast operator. -/
def GVarₛ : {Γₛ : Conₛ} -> (γₛE : ConₛA (EConₛ Γₛ)) ->
  (v : Varₛ Γₛ Aₛ) ->
  Varₛ (GConₛ Γₛ γₛE) (GTyₛ Aₛ (VarₛA (EVarₛ v) γₛE))
| _ ▹ _, _       , .vz   => .vz
| _ ▹ _, ⟨γₛE, _⟩, .vs v => .vs (GVarₛ γₛE v)


/-- Given `Γₛ ⊢ Self a₁ a₂ a₃ : U` returns `guard(Γₛ) ⊢ SelfG a₁ a₂ a₃ : SelfE -> U`.

  Challange is that we don't know which type (`Even`, `Odd`, etc) `t` refers to,
  it could be `Even @ 123` or `Odd @ 123`.
  So the output term's type needs to depend on `t`.  -/
def GTmₛ : {Γₛ : Conₛ.{u}} -> (γₛE : ConₛA.{u, u} (EConₛ Γₛ)) ->
  (t : Tmₛ.{u} Γₛ Aₛ) ->
  Tmₛ (GConₛ Γₛ γₛE) (GTyₛ Aₛ (TmₛA (ETmₛ t) γₛE))
| Γₛ, γₛE, .var v              => by
  rw [ETmₛ, TmₛA]
  exact .var (GVarₛ.{u, u} γₛE v)
| Γₛ, γₛE, .app (A := _Aₛ) t u => .app (GTmₛ γₛE t) u

/-- For example maps the `Vec.cons` ctor of type
```
Vec : Nat ->          U ⊢ (n:Nat) -> (_:A) -> (_ : Vec n) ->            Vec (n+1)
```
into `VecG.cons` of type
```
VecG : Nat -> VecE -> U ⊢ (n:Nat) -> (x:A) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons (n+1) x e)
``` -/
def GTyₚ.{u} (γₛE : ConₛA.{u} (EConₛ Γₛ)) : (A : Tyₚ Γₛ) -> (aE : TyₚA.{u, u} (ETyₚ A) γₛE) ->
  Tyₚ (GConₛ Γₛ γₛE)
| El         Self, aE => El (.app (GTmₛ γₛE Self) aE) -- VecG ... (VecE.cons ...)
| PPi   T    Rest, aE => PPi T (fun t => GTyₚ γₛE (Rest t) (aE t))
| PFunc Self Rest, aE => -- this `Self` could be from a different ind type from the mutual block!
    PPi (TmₛA (ETmₛ Self) γₛE) fun e =>  -- (e : SelfE) ->
      PFunc (.app (GTmₛ γₛE Self) e) <| -- SelfG e ->
        GTyₚ γₛE Rest (aE e)

def GConₚ (γₛE : ConₛA (EConₛ Γₛ)) : (Γ : Conₚ Γₛ) -> (γE : ConₚA (EConₚ Γ) γₛE) -> Conₚ (GConₛ Γₛ γₛE)
| ⬝, ⟨⟩ => ⬝
| Γ ▹ A, ⟨γE, aE⟩ => GConₚ γₛE Γ γE ▹ GTyₚ γₛE A aE


/-- Cast `"Vec.cons"` to `"VecG.cons"`, similar to `guardTmₚ`. -/
def GVarₚ : {Γ : Conₚ Γₛ} -> (γₛE : ConₛA (EConₛ Γₛ)) -> (γE : ConₚA (EConₚ Γ) γₛE) ->
  (v : Varₚ Γ A) ->
  Varₚ (GConₚ γₛE Γ γE) (GTyₚ γₛE A (TmₚA (.var <| EVarₚ v) γE))
| _ ▹ _, _  ,       _, .vz   => .vz
| _ ▹ _, γₛE, ⟨γE, _⟩, .vs v => .vs (GVarₚ γₛE γE v)

/-- Given `"Vec.cons n x v" : "Vec n"`, we change it to `"VecG.cons n x v vG" : "VecG n (VecE.cons n x v)"`.
  Here, note that we construct `"vG" : "VecG n v"`; in general for every inductive argument. -/
def GTmₚ (γₛE : ConₛA (EConₛ Γₛ)) (γE : ConₚA (EConₚ Γ) γₛE)
  : (tm : Tmₚ Γ A) ->
    Tmₚ (GConₚ γₛE Γ γE) (GTyₚ γₛE A (TmₚA (ETmₚ tm) γE))
| Tmₚ.var v => .var (GVarₚ γₛE γE v)
| Tmₚ.app (A := _A) t u => .app (GTmₚ γₛE γE t) u
| Tmₚ.appr t u =>
  let e := TmₚA (ETmₚ u) γE
  let g := GTmₚ γₛE γE u
  .appr (.app (GTmₚ γₛE γE t) e) g

#print axioms GTmₚ

-- # Example time!

inductive VecE : Type u where
| nil : VecE
| cons : Nat -> String -> VecE -> VecE

inductive VecG : Nat -> VecE -> Type u where
| nil : VecG 0 .nil
| cons : (n : Nat) -> (x:String) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons n x e)

#reduce GTmₚ (Γₛ := Vₛ) (Γ := V String) ⟨⟨⟩, VecE⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ (.var .vz)
#reduce GTmₚ (Γₛ := Vₛ) (Γ := V String) ⟨⟨⟩, VecE⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ (.var (.vs .vz))

/-- VecG : Nat -> VecE -> Type -/
example : GConₛ Vₛ ⟨⟨⟩, VecE⟩ = (⬝ ▹ SPi Nat fun _ => SPi VecE fun _ => U) := rfl
#reduce GConₚ (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ (V String) ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩

/-
  # Lowering
-/

-- ## Sorts

#check GTyₛ
def LTyₛ : Type (u+1) := Tyₛ.{u} × Tyₛ.{u}
def lTyₛ (A : Tyₛ) : LTyₛ := ⟨ETyₛ A, GTyₛ A γE⟩
def LTyₛA (AL : LTyₛ) : Type _ := TyₛA AL.fst × TyₛA AL.snd
def LConₛ : Type (u+1) := Conₛ.{u} × Conₛ.{u}
def LConₛA (ΓL : LConₛ) : Type _ := ConₛA ΓL.fst × ConₛA ΓL.snd
def LVarₛ : Type (u+1) :=

abbrev LTmₛ {Γₛ : Conₛ} {Aₛ : Tyₛ} (γₛE : ConₛA (EConₛ Γₛ))
  (t : Tmₛ Γₛ Aₛ)
  : Type _
  := Tmₛ (EConₛ Γₛ) U × Tmₛ (GConₛ Γₛ γₛE) (GTyₛ Aₛ (TmₛA (ETmₛ t) γₛE))

/-- For example maps `"Vec 123"` to `⟨("VecE", "VecG 123"⟩`. -/
def lTmₛ {Γₛ : Conₛ} {Aₛ : Tyₛ} (γₛE : ConₛA (EConₛ Γₛ))
  (t : Tmₛ Γₛ Aₛ)
  : LTmₛ γₛE t
  -- : Tmₛ (eraseConₛ Γₛ) U × Tmₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ (TmₛA (eraseTmₛ t) γₛE))
  := ⟨ETmₛ t, GTmₛ γₛE t⟩

/-- We want to obtain the actual `(e : VecE) × VecG e`. -/
def lTmₛA (γₛE : ConₛA.{0, 0} (EConₛ Γₛ)) (γₛG : ConₛA (GConₛ Γₛ γₛE)) (T : Tmₛ Γₛ U) : Type
  := @Sigma (TmₛA (ETmₛ T) γₛE) (TmₛA (GTmₛ γₛE T) γₛG)

/-- `"Vec 123" : "U"` becomes `⟨"VecE", "VecG 123"⟩ : "U" × "VecE -> U"` -/
example : lTmₛ (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ (.app (.var .vz) 123)
  = ⟨.var .vz, .app (.var .vz) 123⟩
  := rfl

example : lTmₛA (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩ (.app (.var .vz) 123)
  = ((e : VecE) × VecG 123 e)
  := rfl


-- ## Points

abbrev LTmₚ {Γₛ : Conₛ} (Γ : Conₚ Γₛ) {A : Tyₚ Γₛ} {γₛE} (γE : ConₚA (EConₚ Γ) γₛE) (t : Tmₚ Γ A)
  : Type _
  := Tmₚ (EConₚ Γ) (ETyₚ A) × Tmₚ (GConₚ γₛE Γ γE) (GTyₚ γₛE A (TmₚA (ETmₚ t) γE))

/-- Given a term `"Vec.cons n x v"`, produce
  `⟨"VecE.cons n x vᴱ", "VecG.cons n x vᴳ"⟩ : Tmₛ ["VecE"] "U" × Tmₛ ["VecG"] "VecE -> U"`. -/
def lTmₚ {Γₛ : Conₛ} {Γ : Conₚ Γₛ} {A : Tyₚ Γₛ} {γₛE} {γE : ConₚA (EConₚ Γ) γₛE}
  (t : Tmₚ Γ A)
  : LTmₚ Γ γE t
  -- : Tmₚ (eraseConₚ Γ) (eraseTyₚ A) × Tmₚ (guardConₚ γₛE Γ γE) (guardTyₚ γₛE A (TmₚA (eraseTmₚ t) γE))
  := ⟨ETmₚ t, GTmₚ γₛE γE t⟩

/-- Given `"Vec.cons ..." : "Vec 123"`, produce `⟨"VecE.cons ...", "VecG.cons ..."⟩ : @Sigma VecE (VecG 123)`. -/
def lTmₚA (γₛE : ConₛA (EConₛ Γₛ)) (γₛG : ConₛA (GConₛ Γₛ γₛE))
  (γE : ConₚA (EConₚ Γ) γₛE) (γG : ConₚA (GConₚ γₛE Γ γE) γₛG)
  (t : Tmₚ Γ (El T))
  : lTmₛA γₛE γₛG T
  := by
    let g := TmₚA (GTmₚ γₛE γE t) γG
    rw [GTyₚ] at g
    rw [TyₚA] at g
    rw [TmₛA] at g
    exact ⟨TmₚA (ETmₚ t) γE, g⟩

example : lTmₚA (Γₛ := Vₛ) (Γ := V String)
  ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
  (.var (.vs .vz))
  = ⟨VecE.nil, VecG.nil⟩ := rfl

example : lTmₚA (Γₛ := Vₛ) (Γ := V String)
  ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩
  ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
  (
    let asdf1 : Tmₚ (V String) (PPi String fun _x => PFunc (.app (Tmₛ.var vz) 0) (El _)) := .app (.var .vz) 0
    let asdf2 : Tmₚ (V String) (                     PFunc (.app (Tmₛ.var vz) 0) (El _)) := .app asdf1 "" -- ! if you inline `asdf1` it breaks
    let asdf3 : Tmₚ (V String) (                                                 (El _)) := .appr asdf2 (.var (.vs .vz))
    asdf3 -- ! if you inline asdf3 is breaks as well
  )
  = ⟨VecE.cons 0 "" VecE.nil, VecG.cons 0 "" VecE.nil VecG.nil⟩
  := rfl


def r : (TyₛA Aₛ) -> TyₛA Aₛ
  := sorry

#check 1

/- # Reconstructing Proofs
  Given `P : Vec n -> Prop`, We can derive `P' : @Sigma VecE (VecG n) -> Prop`.
  And now given `prf' : P' ⟨vE, vG⟩`, we need to find `?prf : P v`.

  So originally we had goal `v : Vec n ⊢ ?prf : P v`.
  We have a `down : Vec n -> Sigma VecE (VecG n)` function, such that `down ∘ up = id`. // down is `lower`
  We derive `P' : Sigma VecE (VecG n) -> Prop`, such that `P' (down v) -> P v`. !!! how "such that"? This is the crucial part.
-/

namespace VecExample
def VecL (n) := @Sigma VecE (VecG n)
def nilL : VecL 0 := ⟨.nil, .nil⟩
def consL : (n : Nat) -> String -> VecL n -> VecL (n + 1)
  := fun n x v => ⟨.cons n x v.fst, .cons n x v.fst v.snd⟩

-- This is `lowerTmₚA`
def down : Vec String n -> VecL n
| .nil => nilL
| .cons n x v => consL n x (down v)

section Useless
  /- We first apply `VecE.rec`, then inside each branch we apply `VecG.rec`. -/
  def up' : (e : VecE) -> VecG n e -> Vec String n
  | .nil        , g => let .nil := g; .nil
  | .cons n x vE, g => let .cons n x vE vG := g; .cons n x (up' vE vG)

  def up : @Sigma VecE (VecG n) -> Vec String n := fun v => up' v.fst v.snd

  theorem Vec.up_down : up (down v) = v := by
    induction v with
    | nil => rfl
    | cons n x v ih => simp_all only [up, up']

  @[simp] theorem Vec.down_eta : ⟨(down v).fst, (down v).snd⟩ = down v := by sorry -- simp [down]
  @[simp] theorem Vec.up_down_eta : up ⟨(down v).fst, (down v).snd⟩ = v := by simp [down_eta, up_down]
  theorem Vec.up'_is_up : up'.{u} (down v).fst (down v).snd = up.{u} ⟨(down v).fst, (down v).snd⟩ := by rw [up]
  @[simp] theorem Vec.up'_down_eta : up' (down v).fst (down v).snd = v := by rw [Vec.up'_is_up, Vec.up_down_eta]
end Useless

@[irreducible] def len  : Vec String n -> Nat := fun _ => n
@[irreducible] def lenL : VecL n       -> Nat := fun _ => n
theorem len_is_lenL (v : Vec String n)           : len v         = lenL (down v) := by unfold len; unfold lenL; rfl
theorem lenL_is_len (vE : VecE) (vG : VecG n vE) : lenL ⟨vE, vG⟩ = len (up ⟨vE, vG⟩) := by unfold len; unfold lenL; rfl

/-- Our original proof goal. -/
def P (v : Vec String n) : Prop := ∀x, len  (.cons n x v) = .succ (len v)
/-- Construct derived proof goal, along with `reconstruct` proof below. -/
def PL.{u} (vL : VecL.{u} n) : Prop := ∀x, lenL (consL n x vL) = .succ (lenL vL)

#check Eq

theorem reconstruct' : PL (down v) -> P v :=
  fun h x => by
    have h := h x
    rw [len_is_lenL] -- we need to get `len_is_lenL` lemmas for each symbol we encounter... will be quite a few.
    rw [len_is_lenL]
    rw [down]
    exact h

-- You'll need to construct two concrete vE and vG such that `h` is true. But they're just `down` evaluated.
theorem reconstruct (h : ⟨vE, vG⟩ = down v) : PL ⟨vE, vG⟩ -> P v := by rw [h]; exact reconstruct'

end VecExample

-- And now we are done. If the original goal has been `v : Vec n ⊢ ?g : P v`,
-- then we can close it with `?g := reconstruct _ ?g'`, where `vE, vG ⊢ ?g' : P' ⟨vE, vG⟩`,
-- and then give `?g'` to the smt solver.
-- Time to generalize!

-- ! This is just "up"... but we want something for arbitrary formulas
def up : (T : Tmₛ Γₛ U) -> lTmₛA γₛE γₛG T -> TmₛA T γₛ :=
  sorry

-- * Need some way to express types such as `∀x, ... = ...` as terms in order to pattern match on them.
def reconstruct : (T : Tmₛ Γₛ U) -> lTmₛA γₛE γₛG T -> TmₛA T γₛ := sorry

-- ? But can you express our example `Vec.reconstruct` with Tmₚ-based `reconstruct`?
-- ! No, the above is just "up".
def aaa := reconstruct
  (Γₛ := Vₛ) (γₛ := ⟨⟨⟩, Vec String⟩) (γₛE := ⟨⟨⟩, VecE⟩) (γₛG := ⟨⟨⟩, VecG⟩)
  (.app (.var .vz) 123)

/-
  Just imagine that it's a Tm, and how would it work then. The key will be iterating over the context
  I think, since that's where all the inductive types with indices come from.
  So then you just do induction over the context and it should be fine?
  `Γ ⊢ t : A` encoded as `t : Tm Γ A`.
  ? Maybe you can do something with substitutions, since they're basically just morphisms
  ? between contexts? So we want `Tm Γ A` --> `Tm Γ' A'`, where Γ' is the index-erased/guarded ctx.

-/

#check aaa



inductive Ctx : Type where
inductive Ty : Ctx -> Type where
inductive Tm : (Γ : Ctx) -> Ty Γ -> Type 1 where -- these are pre-terms. we'll have to add wellfoundedness later.
| var : Nat -> Tm Γ A
| pi : Type -> Tm Γ A -- TODO The "type" here can't be pattern matched, UNLESS... we somehow reintroduce that via wellfoundedness later.

def Vec.append : Vec α n → Vec α m → Vec α (n + m)
| xs, .nil         => xs
| xs, .cons _ y ys => (append xs (.cons _ y ys))

open Lean Elab Term

def lower : Expr -> MetaM Expr
| .app f a => return .app (<- lower f) (<- lower a)
| .forallE var dom body bi => return .forallE var
| _ => throwError "oh no"

/-- Given `P`, produces `P'` -/
elab "lower! " t:term : term => do
  let tm <- elabTerm t none
  return tm

-- Okay let's assume our env only contains some extremely basic primitives.
#check ∀n, ∀v, lower! ∀x, len (.cons n x v) = .succ (len v)
