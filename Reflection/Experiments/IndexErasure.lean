import Reflection.MutualInductive

namespace Reflection.IndexErasure

open Reflection MutualInductive
open Tyₛ Tyₚ Varₛ Varₚ

-- # Erasure

inductive Example.VecE : Type u where
| nil : VecE
| cons : Nat -> String -> VecE -> VecE

def eTyₛ : Tyₛ.{u} -> Tyₛ.{u}
| _ => U

abbrev ETyₛA Aₛ := TyₛA (eTyₛ Aₛ) -- actually this is a constant `ETyₛA := Type _`

/-- For example maps sort-ctx `[Vec : Nat -> U, ...]` into `[VecE : U, ...]`. -/
def eConₛ : Conₛ.{u} -> Conₛ.{u}
| ⬝      => ⬝
| Γₛ ▹ _ => eConₛ Γₛ ▹ U

abbrev EConₛA.{u, v} Γₛ := ConₛA.{u, v} (eConₛ Γₛ)

abbrev EVarₛ (Γₛ : Conₛ) : Type _ := Varₛ (eConₛ Γₛ) U

/-- This is a no-op, other than changing the type of the variable. -/
def eVarₛ : Varₛ Γₛ Aₛ -> Varₛ (eConₛ Γₛ) U
| .vz   => .vz
| .vs v => .vs (eVarₛ v)

abbrev ETmₛ (Γₛ : Conₛ) : Type _ := Tmₛ (eConₛ Γₛ) U

/-- For example maps `Vec : Nat -> U ⊢ Vec 123 : U` into `VecE : U ⊢ VecE : U`. -/
def eTmₛ : Tmₛ Γₛ Aₛ -> Tmₛ (eConₛ Γₛ) U
| .var v              => .var (eVarₛ v)
| .app (A := _Aₛ) t u => eTmₛ t

abbrev ETmₛA.{u, v} (T : Tmₛ.{u} Γₛ Aₛ) (γₛE : EConₛA.{u, v} Γₛ) : Type _ := TmₛA.{u, v} (eTmₛ.{u} T) γₛE

abbrev ETyₚ (Γₛ : Conₛ) : Type _ := Tyₚ (eConₛ Γₛ)

/-- For example for `Vec.nil`, maps `Vec : Nat -> U ⊢ Vec 0` into `VecE : U ⊢ VecE`,
and for `Vec.cons` maps `Vec : Nat -> U ⊢ (n:Nat) -> α -> Vec n -> Vec (n+1)`
into `VecE : U ⊢ (n:Nat) -> α -> VecE -> VecE`. -/
def eTyₚ {Γₛ : Conₛ} : Tyₚ Γₛ -> Tyₚ (eConₛ Γₛ)
| El         Self => El (eTmₛ Self)
| PPi   T    Rest => PPi T (fun t => eTyₚ (Rest t))
| PFunc Self Rest => PFunc (eTmₛ Self) (eTyₚ Rest)

abbrev ETyₚA (A : Tyₚ Γₛ) (γₛE : EConₛA Γₛ) : Type _ := TyₚA (eTyₚ A) γₛE

abbrev EConₚ (Γₛ : Conₛ) : Type _ := Conₚ (eConₛ Γₛ)
def eConₚ : Conₚ Γₛ -> Conₚ (eConₛ Γₛ)
| ⬝ => ⬝
| Γ ▹ A => (eConₚ Γ) ▹ (eTyₚ A)

abbrev EConₚA (Γ : Conₚ Γₛ) (γₛE : EConₛA Γₛ) : Type _ := ConₚA (eConₚ Γ) γₛE

abbrev EVarₚ (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) : Type _ := Varₚ (eConₚ Γ) (eTyₚ A)
def eVarₚ : Varₚ Γ A -> Varₚ (eConₚ Γ) (eTyₚ A)
| .vz => .vz
| .vs v => .vs (eVarₚ v)

abbrev ETmₚ (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) : Type _ := Tmₚ (eConₚ Γ) (eTyₚ A)
def eTmₚ : Tmₚ Γ A -> Tmₚ (eConₚ Γ) (eTyₚ A)
| .var v => .var (eVarₚ v)
| .app (A := _A) t u => .app (eTmₚ t) u
| .appr t u => .appr (eTmₚ t) (eTmₚ u)




-- # Guard

inductive Example.VecG : Nat -> VecE -> Type u where
| nil : VecG 0 .nil
| cons : (n : Nat) -> (x:String) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons n x e)

/-- For example maps `Vec : Nat -> U` to `VecG : Nat -> VecE -> U`.
  Note that `∀Aₛ, TyₛA (eraseTyₛ Aₛ) = Type`. -/
-- def guardTyₛ : (Aₛ : Tyₛ.{u}) -> TyₛA.{u, u} (eraseTyₛ Aₛ) -> Tyₛ.{u}
def gTyₛ : (Aₛ : Tyₛ.{u}) -> Type u -> Tyₛ.{u}
| U         , aₛE => SPi aₛE (fun _ => U)
| SPi T Rest, aₛE => SPi T   (fun t => gTyₛ (Rest t) aₛE)

abbrev GTyₛA.{u, v} Aₛ aₛE := TyₛA.{u, v} (gTyₛ Aₛ aₛE)

/-- For example maps sort-stx `[Vec : Nat -> U]` into `[VecG : Nat -> VecE -> U]`. -/
def gConₛ.{u} : (Γₛ : Conₛ.{u}) -> (γₛE : ConₛA.{u, u} (eConₛ Γₛ)) -> Conₛ.{u}
| ⬝      , ⟨⟩         => ⬝
| Γₛ ▹ Aₛ, ⟨γₛE, aₛE⟩ => Conₛ.ext (gConₛ Γₛ γₛE) (gTyₛ Aₛ aₛE)

abbrev GConₛA (Γₛ : Conₛ.{u}) (γₛE : EConₛA Γₛ) := ConₛA (gConₛ Γₛ γₛE)

/-- VecG : Nat -> VecE -> Type -/
example : gConₛ Vₛ ⟨⟨⟩, VecE⟩ = (⬝ ▹ SPi Nat fun _ => SPi VecE fun _ => U) := rfl

/-- Given a variable `Vec:N->U ⊢ VAR(Vec) : N->U`, we return `VecG:N->VecE->U ⊢ VAR(VecG) : N->VecE->U`.
  The runtime de-brujin value of this variable doesn't change. So this is basically just a cast operator. -/
def gVarₛ : {Γₛ : Conₛ} -> (γₛE : ConₛA (eConₛ Γₛ)) ->
  (v : Varₛ Γₛ Aₛ) ->
  Varₛ (gConₛ Γₛ γₛE) (gTyₛ Aₛ (VarₛA (eVarₛ v) γₛE))
| _ ▹ _, _       , .vz   => .vz
| _ ▹ _, ⟨γₛE, _⟩, .vs v => .vs (gVarₛ γₛE v)

abbrev GTmₛ (Γₛ : Conₛ) (Aₛ : Tyₛ) (γₛE : ConₛA (eConₛ Γₛ)) (tE : ETmₛ Γₛ) : Type _
  := Tmₛ (gConₛ Γₛ γₛE) (gTyₛ Aₛ (TmₛA tE γₛE))

/-- Given `Γₛ ⊢ Self a₁ a₂ a₃ : U` returns `guard(Γₛ) ⊢ SelfG a₁ a₂ a₃ : SelfE -> U`.

  Challange is that we don't know which type (`Even`, `Odd`, etc) `t` refers to,
  it could be `Even @ 123` or `Odd @ 123`.
  So the output term's type needs to depend on `t`.  -/
def gTmₛ : {Γₛ : Conₛ} -> (γₛE : ConₛA.{0, 0} (eConₛ Γₛ)) ->
  (t : Tmₛ Γₛ Aₛ) -> Tmₛ (gConₛ Γₛ γₛE) (gTyₛ Aₛ (TmₛA (eTmₛ t) γₛE))
| Γₛ, γₛE, .var v              => by rw [eTmₛ, TmₛA]; exact .var (gVarₛ γₛE v)
| Γₛ, γₛE, .app (A := _Aₛ) t u => .app (gTmₛ γₛE t) u

abbrev GTmₛA (T : Tmₛ Γₛ Aₛ) (γₛE : EConₛA Γₛ) (γₛG : GConₛA.{0,0} Γₛ γₛE) : GTyₛA Aₛ (ETmₛA T γₛE) := TmₛA (gTmₛ γₛE T) γₛG

abbrev GTyₚ (Γₛ : Conₛ) (γₛE : EConₛA Γₛ) : Type _ := Tyₚ (gConₛ Γₛ γₛE)

/-- For example maps the `Vec.cons` ctor of type
```
Vec : Nat ->          U ⊢ (n:Nat) -> (_:A) -> (_ : Vec n) ->            Vec (n+1)
```
into `VecG.cons` of type
```
VecG : Nat -> VecE -> U ⊢ (n:Nat) -> (x:A) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons (n+1) x e)
``` -/
def gTyₚ (γₛE : ConₛA.{0} (eConₛ Γₛ)) : (A : Tyₚ Γₛ) -> (aE : TyₚA (eTyₚ A) γₛE) ->
  Tyₚ (gConₛ Γₛ γₛE)
| El         Self, aE => El (.app (gTmₛ γₛE Self) aE) -- VecG ... (VecE.cons ...)
| PPi   T    Rest, aE => PPi T (fun t => gTyₚ γₛE (Rest t) (aE t))
| PFunc Self Rest, aE => -- this `Self` could be from a different ind type from the mutual block!
    PPi (TmₛA (eTmₛ Self) γₛE) fun e =>  -- (e : SelfE) ->
      PFunc (.app (gTmₛ γₛE Self) e) <| -- SelfG e ->
        gTyₚ γₛE Rest (aE e)

abbrev GTyₚA (A : Tyₚ Γₛ) (γₛE : EConₛA Γₛ) (γₛG : GConₛA Γₛ γₛE) (aE : TyₚA (eTyₚ A) γₛE) : Type _ := TyₚA (gTyₚ γₛE A aE) γₛG

set_option pp.universes true in
def gConₚ (γₛE : ConₛA (eConₛ Γₛ)) : (Γ : Conₚ Γₛ) -> (γE : ConₚA (eConₚ Γ) γₛE) -> Conₚ (gConₛ Γₛ γₛE)
| ⬝, ⟨⟩ => ⬝
| Γ ▹ A, ⟨γE, aE⟩ => gConₚ γₛE Γ γE ▹ gTyₚ γₛE A aE

abbrev GConₚA (Γ : Conₚ Γₛ) (γₛE : EConₛA Γₛ) (γₛG : GConₛA Γₛ γₛE) (γₚE : ConₚA (eConₚ Γ) γₛE) : Type _ := ConₚA (gConₚ γₛE Γ γₚE) γₛG

/-- Cast `"Vec.cons"` to `"VecG.cons"`, similar to `guardTmₚ`. -/
def gVarₚ : {Γ : Conₚ Γₛ} -> (γₛE : ConₛA (eConₛ Γₛ)) -> (γE : ConₚA (eConₚ Γ) γₛE) ->
  (v : Varₚ Γ A) ->
  Varₚ (gConₚ γₛE Γ γE) (gTyₚ γₛE A (TmₚA (.var <| eVarₚ v) γE))
| _ ▹ _, _  ,       _, .vz   => .vz
| _ ▹ _, γₛE, ⟨γE, _⟩, .vs v => .vs (gVarₚ γₛE γE v)

/-- Given `"Vec.cons n x v" : "Vec n"`, we change it to `"VecG.cons n x v vG" : "VecG n (VecE.cons n x v)"`.
  Here, note that we construct `"vG" : "VecG n v"`; in general for every inductive argument. -/
def gTmₚ (γₛE : ConₛA (eConₛ Γₛ)) (γE : ConₚA (eConₚ Γ) γₛE)
  : (tm : Tmₚ Γ A) ->
    Tmₚ (gConₚ γₛE Γ γE) (gTyₚ γₛE A (TmₚA (eTmₚ tm) γE))
| Tmₚ.var v => .var (gVarₚ γₛE γE v)
| Tmₚ.app (A := _A) t u => .app (gTmₚ γₛE γE t) u
| Tmₚ.appr t u =>
  let e := TmₚA (eTmₚ u) γE
  let g := gTmₚ γₛE γE u
  .appr (.app (gTmₚ γₛE γE t) e) g

abbrev GTmₚ (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) (γₛE : EConₛA Γₛ) (γₚE : ConₚA (eConₚ Γ) γₛE) (tE : ETmₚ Γ A) : Type _
  := Tmₚ (gConₚ γₛE Γ γₚE) (gTyₚ γₛE A (TmₚA tE γₚE))

set_option pp.fieldNotation false in
section
open Example
#reduce gTmₚ (Γₛ := Vₛ) (Γ := V String) ⟨⟨⟩, VecE⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ (.var .vz)
#reduce gTmₚ (Γₛ := Vₛ) (Γ := V String) ⟨⟨⟩, VecE⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ (.var (.vs .vz))
#reduce gConₚ (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ (V String) ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩
end

/-
  # Lowering
-/

@[instance] def IsSimpleTy.decide' (Aₛ : Tyₛ) : Decidable (Aₛ = U)
  := match h : Aₛ with
    | U => .isTrue (by cases h; rfl)
    | SPi .. => .isFalse (by simp only [h, not_false_eq_true])
@[instance] def IsSimple.decide' : (Γₛ : Conₛ) -> Decidable (Γₛ = eConₛ Γₛ)
| ⬝ => .isTrue rfl
| Γₛ ▹ Aₛ =>
  match hAₛ : Aₛ with
  | U =>
    match decide' Γₛ with
    | .isTrue p => by
      rw [eConₛ]
      rw [<- p]
      exact .isTrue rfl
    | .isFalse p => by
      cases hAₛ
      simp_all [eConₛ]
      exact inferInstance
  | SPi _ _ => .isFalse (by simp only [eConₛ, Conₛ.ext.injEq, and_false, not_false_eq_true])
/-- If the type is already simple, we don't need to lower it. -/
def IsSimpleTy (Aₛ : Tyₛ) : Prop := Aₛ = U
/-- If the type is already simple, we don't need to lower it. -/
def IsSimple (Γₛ : Conₛ) : Prop := Γₛ = eConₛ Γₛ
@[instance] def IsSimpleTy.decide (Aₛ : Tyₛ) : Decidable (IsSimpleTy Aₛ) := by unfold IsSimpleTy; exact inferInstance
@[instance] def IsSimple.decide (Γₛ : Conₛ) : Decidable (IsSimple Γₛ) := by unfold IsSimple; exact inferInstance

-- ## Lowering Sorts

-- abbrev LTyₛA.{u, v, w} (Aₛ : Tyₛ.{max u v}) : Type ((max u v w) + 1) :=
--   if Aₛ = U
--     then TyₛA Aₛ
--     else (aₛE : ETyₛA.{max u v, v} Aₛ) × GTyₛA.{max u v, w} Aₛ aₛE

abbrev LTyₛA.{u, v, w} (Aₛ : Tyₛ.{max u v}) : Type ((max u v w) + 1) := (aₛE : ETyₛA.{max u v, v} Aₛ) × GTyₛA.{max u v, w} Aₛ aₛE
abbrev LConₛA (Γₛ : Conₛ)                            : Type _ := (γₛE : EConₛA Γₛ) × GConₛA Γₛ γₛE
abbrev LTmₛ (Γₛ : Conₛ) (Aₛ : Tyₛ) (γₛE : EConₛA Γₛ) : Type _ := (tE  : ETmₛ Γₛ)   × GTmₛ Γₛ Aₛ γₛE tE
abbrev LTmₛA {Γₛ : Conₛ} (T : Tmₛ Γₛ U) (γₛE : EConₛA Γₛ) (γₛG : GConₛA Γₛ γₛE) : Type _ :=
  (e : ETmₛA T γₛE) × GTmₛA T γₛE γₛG e

/-- For example maps `"Vec 123"` to `⟨"VecE", "VecG 123"⟩`. -/
def lTmₛ {Γₛ : Conₛ} {Aₛ : Tyₛ} (γₛE : ConₛA (eConₛ Γₛ)) (t : Tmₛ Γₛ Aₛ) : LTmₛ Γₛ Aₛ γₛE
  := ⟨eTmₛ t, gTmₛ γₛE t⟩

/-- We want to obtain the actual `(e : VecE) × VecG e`. -/
def lTmₛA (γₛE : ConₛA.{0, 0} (eConₛ Γₛ)) (γₛG : ConₛA (gConₛ Γₛ γₛE)) (T : Tmₛ Γₛ U) : Type _
  := @Sigma (ETmₛA T γₛE) (GTmₛA T γₛE γₛG)

set_option pp.universes true in

/-- Construct new inductive types. -/
def lConₛA : (Γₛ : Conₛ) -> (Γₚ : Conₚ Γₛ) -> LConₛA.{0,0} Γₛ
| Γₛ, Γₚ =>
  let γₛE : EConₛA Γₛ     := mkConₛ (Ω := eConₚ Γₚ)
  let γₛG : GConₛA Γₛ γₛE := mkConₛ (Ω := gConₚ γₛE Γₚ)
  -- ⟨γₛE, γₛG⟩
  sorry -- the above works, modulo universe shenanigans

-- ## Lowering Points

abbrev LTyₚA (A : Tyₚ Γₛ) (γₛL : LConₛA Γₛ) : Type _ := (e : ETyₚA A γₛL.fst) × GTyₚA A γₛL.fst γₛL.snd e
abbrev LConₚA (Γ : Conₚ Γₛ) (γₛL : LConₛA Γₛ) : Type _ := (e : EConₚA Γ γₛL.fst) × GConₚA Γ γₛL.fst γₛL.snd e
abbrev LTmₚ {Γₛ : Conₛ} (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) (γₛE) (γₚE : ConₚA (eConₚ Γ) γₛE) : Type _
  := (tE : ETmₚ Γ A) × GTmₚ Γ A γₛE γₚE tE

/-- Given a term `"Vec.cons n x v"`, produce
  `⟨"VecE.cons n x vᴱ", "VecG.cons n x vᴱ vᴳ"⟩ : Tmₛ ["VecE"] "U" × Tmₛ ["VecG"] "VecE -> U"`. -/
def lTmₚ {Γₛ : Conₛ} {Γ : Conₚ Γₛ} {A : Tyₚ Γₛ} {γₛE} {γₚE : ConₚA (eConₚ Γ) γₛE}
  (t : Tmₚ Γ A) : LTmₚ Γ A γₛE γₚE
  := ⟨eTmₚ t, gTmₚ γₛE γₚE t⟩

/-- Given `"Vec.cons ..." : "Vec 123"`, produce `⟨VecE.cons ..., VecG.cons ...⟩ : @Sigma VecE (VecG 123)`. -/
def lTmₚA (γₛE : ConₛA (eConₛ Γₛ)) (γₛG : ConₛA (gConₛ Γₛ γₛE))
  (γE : ConₚA (eConₚ Γ) γₛE) (γG : ConₚA (gConₚ γₛE Γ γE) γₛG)
  (t : Tmₚ Γ (El T))
  : lTmₛA γₛE γₛG T
  := by
    let g := TmₚA (gTmₚ γₛE γE t) γG
    rw [gTyₚ] at g
    rw [TyₚA] at g
    rw [TmₛA] at g
    exact ⟨TmₚA (eTmₚ t) γE, g⟩

section
  open Example
  -- Sorts
  example : LConₛA Vₛ = ((γₛE : PUnit.{2} × Type) × (PUnit.{2} × (Nat → γₛE.snd → Type))) := rfl
  example : LConₛA Vₛ := ⟨⟨⟨⟩, VecE⟩, ⟨⟨⟩, VecG⟩⟩
  /-- `"Vec 123" : "U"` becomes `⟨"VecE", "VecG 123"⟩ : "U" × "VecE -> U"` -/
  example : lTmₛ  (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩            (.app (.var .vz) 123) = ⟨.var .vz, .app (.var .vz) 123⟩ := rfl
  example : lTmₛA (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩ (.app (.var .vz) 123) = @Sigma VecE (VecG 123)          := rfl

  -- Points
  example : lTmₚA (Γₛ := Vₛ) (Γ := V String)
    ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
    (.var (.vs .vz))
    = ⟨VecE.nil, VecG.nil⟩ := rfl
  example : lTmₚA (Γₛ := Vₛ) (Γ := V String)
    ⟨⟨⟩, VecE⟩                  ⟨⟨⟩, VecG⟩
    ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
    (
      let asdf1 : Tmₚ (V String) (PPi String fun _x => PFunc (.app (Tmₛ.var vz) 0) (El _)) := .app (.var .vz) 0
      let asdf2 : Tmₚ (V String) (                     PFunc (.app (Tmₛ.var vz) 0) (El _)) := .app asdf1 "" -- ! if you inline `asdf1` it breaks
      let asdf3 : Tmₚ (V String) (                                                 (El _)) := .appr asdf2 (.var (.vs .vz))
      asdf3 -- ! if you inline asdf3 is breaks as well
    )
    = ⟨VecE.cons 0 "" VecE.nil, VecG.cons 0 "" VecE.nil VecG.nil⟩
    := rfl
end



/- # Reconstruction for Mutually Inductive Types
  Given `P : Vec n -> Prop`, We can derive `P' : @Sigma VecE (VecG n) -> Prop`.
  And now given `prf' : P' ⟨vE, vG⟩`, we need to find `?prf : P v`.

  So originally we had goal `v : Vec n ⊢ ?prf : P v`.
  We have a `down : Vec n -> Sigma VecE (VecG n)` function, such that `down ∘ up = id`. // down is `lower`
  We derive `P' : Sigma VecE (VecG n) -> Prop`, such that `P' (down v) -> P v`. !!! how "such that"? This is the crucial part.
-/

-- This is just `rTyₛA {Aₛ} _ ≣ TyₛA Aₛ` ?
def rTyₛA : {Aₛ : Tyₛ} -> LTyₛA.{0,0,0} Aₛ -> TyₛA Aₛ
| U      , _      => Type
| SPi X _, ⟨E, G⟩ => fun (x : X) => rTyₛA ⟨E, G x⟩

def rConₛA : {Γₛ : Conₛ} -> LConₛA Γₛ -> ConₛA Γₛ
| ⬝    , ⟨⟨⟩, ⟨⟩⟩ => ⟨⟩
| _ ▹ _, ⟨⟨γE, aE⟩, ⟨γG, aG⟩⟩ => ⟨rConₛA ⟨γE, γG⟩, rTyₛA ⟨aE, aG⟩⟩

-- * I think the idea should be to provide an eliminator for L, which is exactly as powerful
-- * as the original eliminator.

def rTyₛD : (Aₛ : Tyₛ) -> (aₛL : LTyₛA Aₛ) -> (eD : TyₛD (eTyₛ Aₛ) aₛL.fst) × TyₛD (gTyₛ Aₛ aₛL.fst) aₛL.snd
| U       , τ => sorry
| SPi X Bₛ, f => sorry
-- def rTyₛD : (Aₛ : Tyₛ) -> (aₛE : ETyₛA Aₛ) -> (aₛG : GTyₛA Aₛ aₛE) -> (eD : TyₛD (eTyₛ Aₛ) aₛE) × TyₛD (gTyₛ Aₛ aₛE) aₛG
-- | U       , τ => sorry
-- | SPi X Bₛ, f => sorry

def rEConₛD : (Γₛ : Conₛ) -> (γₛE : EConₛA Γₛ) -> ConₛD (eConₛ Γₛ) γₛE
| ⬝, ⟨⟩ => ⟨⟩
| Γₛ ▹ Aₛ, ⟨a, b⟩ => ⟨rEConₛD Γₛ a, rTyₛD Aₛ b⟩

#check mkConₛ
#check elimConₛ

def rTyₚA : {A : Tyₚ Γₛ} -> LTyₚA A γₛL -> TyₚA A γₛ
| El T, ⟨aE, aG⟩ =>
  -- aE : ETyₚA (El T) γₛL.fst
  -- aG : GTyₚA (El T) γₛL.fst γₛL.snd aE
  -- elimE (motive := (aE : ETyₚA (El T) γₛL.fst) -> GTyₚA (El T) γₛL.fst γₛL.snd aE -> TyₚA (El T) γₛ)
  let eDₛ : ConₛD (eConₛ Γₛ) γₛL.fst := fun x => sorry
  let eDₚ : TyₚD (eTyₚ (El T)) eDₛ aE := sorry
  -- Now given D, we can obtain S.
  let eSₛ : ConₛS (eConₛ Γₛ) γₛL.fst eDₛ := elimConₛ eDₛ
  sorry
| PPi T B, aL => fun x => sorry
| PFunc A B, aL => fun x => sorry

def rConₚA : {Γ : Conₚ Γₛ} -> LConₚA Γ γₛL -> ConₚA Γ γₛ
| Γ, γₚL => sorry

namespace Example
  def VecL (n) := @Sigma VecE (VecG n)
  def nilL : VecL 0 := ⟨.nil, .nil⟩
  def consL : (n : Nat) -> String -> VecL n -> VecL (n + 1)
    := fun n x v => ⟨.cons n x v.fst, .cons n x v.fst v.snd⟩

  set_option linter.unusedVariables false in
  /-- You can specify an eliminator for VecL, which behaves exactly the way that Vec.rec does. -/
  noncomputable def VecL.elim
    {motive : (n : Nat) -> VecL n -> Sort u}
    (nilD : motive 0 nilL)
    (consD : (n : Nat) -> (x : String) -> (vL : VecL n) -> motive n vL -> motive (n + 1) (consL n x vL))
    (n : Nat)
    (vL : VecL n)
    : motive n vL :=
    @VecE.rec (fun vE => (vG : VecG n vE) -> motive n ⟨vE, vG⟩)
      (fun vG =>
        @VecG.rec (fun n vE vG => motive n ⟨vE, vG⟩)
          nilD
          (fun n x vE vG ih_g => consD n x ⟨vE, vG⟩ ih_g)
          n
          .nil
          vG
      )
      (fun n' x vE ih_e vG =>
        @VecG.rec (fun n vE vG => motive n ⟨vE, vG⟩)
          nilD
          (fun n x vE vG ih_g => consD n x ⟨vE, vG⟩ ih_g)
          n
          (VecE.cons n' x vE)
          vG
      )
      vL.fst
      vL.snd

  def down : Vec String n -> VecL n
  | .nil => nilL
  | .cons n x v => consL n x (down v)

  /- We first apply `VecE.rec`, then inside each branch we apply `VecG.rec`. -/
  def up_lean : (e : VecE) -> VecG n e -> Vec String n
  | .nil        , g => let .nil := g; .nil
  | .cons n x vE, g => let .cons n x vE vG := g; .cons n x (up_lean vE vG)

  set_option linter.unusedVariables false in
  noncomputable def up_recErecG : (e : VecE) -> VecG n e -> Vec String n :=
    @VecE.rec (fun vE => (vG : VecG n vE) -> Vec String n)
      (fun g =>
        @VecG.rec (fun n e g => Vec String n)
          (Vec.nil)
          (fun n x e g ih_g => Vec.cons n x ih_g)
          n
          .nil
          g
      )
      (fun n' x e ih_e g =>
        @VecG.rec (fun n e g => Vec String n)
          (Vec.nil)
          (fun n x e g ih_g => Vec.cons n x ih_g)
          n
          (.cons n' x e)
          g
      )

  /-- Using VecL.elim we can do the above much nicer. -/
  noncomputable def up_recL : {n : Nat} -> (vL : VecL n) -> Vec String n :=
    @VecL.elim (fun n _vL => Vec String n)
      Vec.nil
      (fun n x _vL ih => Vec.cons n x ih)

  noncomputable abbrev up := @up_recL

  -- theorem Vec.up_down : up (down v) = v := by
  --   induction v with
  --   | nil => rfl
  --   | cons n x v ih => simp_all only [up, up_recL, VecL.elim, <- ih]; sorry
  -- @[simp] theorem Vec.down_eta : ⟨(down v).fst, (down v).snd⟩ = down v := by sorry -- simp [down]
  -- @[simp] theorem Vec.up_down_eta : up ⟨(down v).fst, (down v).snd⟩ = v := by simp [down_eta, up_down]
  -- theorem Vec.up'_is_up : up_lean.{u} (down v).fst (down v).snd = up.{u} ⟨(down v).fst, (down v).snd⟩ := by simp [up, up_recL, VecL.elim]
  -- @[simp] theorem Vec.up'_down_eta : up_lean (down v).fst (down v).snd = v := by rw [Vec.up'_is_up, Vec.up_down_eta]
end Example




/-
  # Reconstruction for whole Formulas
  Ideally you'd have a term model, but that is considerable effort, requiring its own `Con`, `Ty`,
  `Tm`, `Subst`, and inductive-inductive types.
  So we just do this via good old metaprogramming, for now.
-/

namespace Example
  @[irreducible] def len  : Vec String n -> Nat := fun _ => n
  @[irreducible] def lenL : VecL n       -> Nat := fun _ => n
  theorem len_is_lenL (v : Vec String n) : len v   = lenL (down v) := by unfold len; unfold lenL; rfl
  theorem lenL_is_len (vL : VecL n)      : lenL vL = len (up vL) := by unfold len; unfold lenL; rfl

  /-- Our original proof goal. -/
  def P (v : Vec String n) : Prop := ∀x, len (.cons n x v) = .succ (len v)
  /-- Construct derived proof goal, along with `reconstruct` proof below. -/
  def PL.{u} (vL : VecL.{u} n) : Prop := ∀x, lenL (consL n x vL) = .succ (lenL vL)

  theorem reconstruct' : PL (down v) -> P v :=
    fun h x => by
      have h := h x
      rw [len_is_lenL] -- we need to get `len_is_lenL` lemmas for each symbol we encounter... will be quite a few.
      rw [len_is_lenL]
      rw [down]
      exact h

  -- You'll need to construct two concrete vE and vG such that `h` is true. But they're just `down` evaluated.
  theorem reconstruct (h : vL = down v) : PL vL -> P v := by rw [h]; exact reconstruct'

  -- And now we are done. If the original goal has been `v : Vec n ⊢ ?g : P v`,
  -- then we can close it with `?g := reconstruct _ ?g'`, where `vE, vG ⊢ ?g' : P' ⟨vE, vG⟩`,
  -- and then give `?g'` to the smt solver.
  -- Time to generalize!
end Example

-- * Need some way to express types such as `∀x, ... = ...` as terms in order to pattern match on them.
def reconstruct : (T : Tmₛ Γₛ U) -> lTmₛA γₛE γₛG T -> TmₛA T γₛ := sorry

-- ? But can you express our example `Vec.reconstruct` with Tmₚ-based `reconstruct`?
-- ! No, the above is just "up".
def aaa := reconstruct
  (Γₛ := Vₛ) (γₛ := ⟨⟨⟩, Vec String⟩) (γₛE := ⟨⟨⟩, Example.VecE⟩) (γₛG := ⟨⟨⟩, Example.VecG⟩)
  (.app (.var .vz) 123)

#check aaa


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
