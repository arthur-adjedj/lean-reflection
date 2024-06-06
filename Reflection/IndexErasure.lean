import Reflection.MutualInductive
import Qq

namespace Reflection.IndexErasure

set_option pp.fieldNotation false
-- set_option pp.universes true

open Reflection MutualInductive
open Tyₛ Tyₚ Varₛ Varₚ

-- # Erasure

def eTyₛ : Tyₛ.{u} -> Tyₛ.{u}
| _ => U

/-- For example maps sort-ctx `[Vec : Nat -> U, ...]` into `[VecE : U, ...]`. -/
def eConₛ : Conₛ.{u} -> Conₛ.{u}
| ⬝      => ⬝
| Γₛ ▹ _ => eConₛ Γₛ ▹ U

/-- This is a no-op, other than changing the type of the variable. -/
def eVarₛ : Varₛ Γₛ Aₛ -> Varₛ (eConₛ Γₛ) U
| .vz   => .vz
| .vs v => .vs (eVarₛ v)

/-- For example maps `Vec : Nat -> U ⊢ Vec 123 : U` into `VecE : U ⊢ VecE : U`. -/
def eTmₛ : Tmₛ Γₛ Aₛ -> Tmₛ (eConₛ Γₛ) U
| .var v              => .var (eVarₛ v)
| .app (A := _Aₛ) t u => eTmₛ t

/-- For example for `Vec.nil`, maps `Vec : Nat -> U ⊢ Vec 0` into `VecE : U ⊢ VecE`,
and for `Vec.cons` maps `Vec : Nat -> U ⊢ (n:Nat) -> α -> Vec n -> Vec (n+1)`
into `VecE : U ⊢ (n:Nat) -> α -> VecE -> VecE`. -/
def eTyₚ {Γₛ : Conₛ} : Tyₚ Γₛ -> Tyₚ (eConₛ Γₛ)
| El         Self => El (eTmₛ Self)
| PPi   T    Rest => PPi T (fun t => eTyₚ (Rest t))
| PFunc Self Rest => PFunc (eTmₛ Self) (eTyₚ Rest)

def eConₚ : Conₚ Γₛ -> Conₚ (eConₛ Γₛ)
| ⬝ => ⬝
| Γ ▹ A => (eConₚ Γ) ▹ (eTyₚ A)

def eVarₚ : Varₚ Γ A -> Varₚ (eConₚ Γ) (eTyₚ A)
| .vz => .vz
| .vs v => .vs (eVarₚ v)

def eTmₚ : Tmₚ.{u, v} Γ A -> Tmₚ.{u, v} (eConₚ Γ) (eTyₚ A)
| .var v => .var (eVarₚ v)
| .app (A := _A) t u => .app (eTmₚ t) u
| .appr t u => .appr (eTmₚ t) (eTmₚ u)

abbrev ETyₛA Aₛ := TyₛA (eTyₛ Aₛ) -- actually this is a constant `ETyₛA := Type _`
abbrev EConₛA.{u, v} Γₛ := ConₛA.{u, v} (eConₛ Γₛ)
abbrev EVarₛ (Γₛ : Conₛ) : Type _ := Varₛ (eConₛ Γₛ) U
abbrev ETmₛ (Γₛ : Conₛ) : Type _ := Tmₛ (eConₛ Γₛ) U
abbrev ETmₛA.{u, v} (T : Tmₛ.{u} Γₛ Aₛ) (γₛE : EConₛA.{u, v} Γₛ) : Type _ := TmₛA.{u, v} (eTmₛ.{u} T) γₛE
abbrev mkETyₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₛ : Tyₛ} (t : Tmₛ Ωₛ Aₛ) : TyₛA.{u, u+1} U.{u} := mkTyₛ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ) (eTmₛ t)
abbrev mkEConₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) : EConₛA.{u, u+1} Ωₛ                 := mkConₛ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ)

abbrev ETyₚ (Γₛ : Conₛ) : Type _ := Tyₚ (eConₛ Γₛ)
abbrev ETyₚA (A : Tyₚ Γₛ) (γₛE : EConₛA Γₛ) : Type _ := TyₚA (eTyₚ A) γₛE
abbrev EConₚ (Γₛ : Conₛ) : Type _ := Conₚ (eConₛ Γₛ)
abbrev EConₚA (Γ : Conₚ Γₛ) (γₛE : EConₛA Γₛ) : Type _ := ConₚA (eConₚ Γ) γₛE
abbrev EVarₚ (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) : Type _ := Varₚ (eConₚ Γ) (eTyₚ A)
abbrev ETmₚ (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) : Type _ := Tmₚ (eConₚ Γ) (eTyₚ A)
abbrev mkETyₚ.{u} (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₚ : Tyₚ Ωₛ} (t : Tmₚ Ωₚ Aₚ) : ETyₚA Aₚ (mkEConₛ Ωₛ Ωₚ) := mkTyₚ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ) (eTmₚ t)
abbrev mkEConₚ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) : EConₚA.{u, u+1} Ωₚ (mkEConₛ Ωₛ Ωₚ) := mkConₚ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ)

theorem mkEConₛ_coherent {t : Tmₛ Ωₛ Aₛ} : TmₛA (eTmₛ t) (mkEConₛ Ωₛ Ωₚ) = mkETyₛ Ωₛ Ωₚ t := by
  rw [mkEConₛ, mkETyₛ, mkConₛ]
  rw [mkConₛ_coherent]
  induction t with
  | var v =>
    simp [eTmₛ, TmₛA_var, mkTyₛ]
    induction v with
    | vz => rfl
    | vs v =>
      simp only [eVarₛ, VarₛA]
      rw [SubₛTm]
      rw [SubₛVar_id]
  | app t u ih => rw [eTmₛ, ih]




-- # Guard

/-- For example maps `Vec : Nat -> U` to `VecG : Nat -> VecE -> U`.
  Note that `∀Aₛ, TyₛA (eraseTyₛ Aₛ) = Type`. -/
def gTyₛ : (Aₛ : Tyₛ.{u}) -> TyₛA.{u, u+1} (eTyₛ Aₛ) -> Tyₛ.{u+1}
| U         , aₛE => SPi aₛE             (fun _ => U)
| SPi T Rest, aₛE => SPi (ULift.{u+1} T) (fun t => gTyₛ (Rest t.down) aₛE)

/-- For example maps sort-stx `[Vec : Nat -> U]` into `[VecG : Nat -> VecE -> U]`. -/
def gConₛ : (Γₛ : Conₛ.{u}) -> (γₛE : ConₛA.{u, u+1} (eConₛ.{u} Γₛ)) -> Conₛ.{u+1}
| ⬝      , ⟨⟩         => ⬝
| Γₛ ▹ Aₛ, ⟨γₛE, aₛE⟩ => Conₛ.ext (gConₛ Γₛ γₛE) (gTyₛ Aₛ aₛE)
-- /-- VecG : Nat -> VecE -> Type -/
-- example : gConₛ Vₛ ⟨⟨⟩, VecE⟩ = (⬝ ▹ SPi Nat fun _ => SPi VecE fun _ => U) := rfl

example : gConₛ ⬝ ⟨⟩ = .nil := rfl
example : gConₛ (Γₛ ▹ Aₛ) ⟨γ, a⟩ = (gConₛ Γₛ γ) ▹ (gTyₛ Aₛ a) := rfl

/-- Given a variable `Vec:N->U ⊢ VAR(Vec) : N->U`, we return `VecG:N->VecE->U ⊢ VAR(VecG) : N->VecE->U`.
  The runtime de-brujin value of this variable doesn't change. So this is basically just a cast operator. -/
def gVarₛ : {Γₛ : Conₛ} -> (γₛE : EConₛA.{u, u+1} Γₛ) ->
  (v : Varₛ Γₛ Aₛ) ->
  Varₛ (gConₛ Γₛ γₛE) (gTyₛ Aₛ (VarₛA (eVarₛ v) γₛE))
| Γₛ ▹ Aₛ, ⟨γₛE, bₛE⟩       , .vz   => by rw [gConₛ]; exact .vz
| _ ▹ _, ⟨γₛE, _⟩, .vs v => .vs (gVarₛ γₛE v)
--   Varₛ (gConₛ Γₛ (mkEConₛ Γₛ Γₚ)) (gTyₛ Aₛ (VarₛA (eVarₛ v) (mkEConₛ Γₛ Γₚ)))
-- | Γₛₛ, _,  .vz   => .vz
-- | Γₛ, Γₚ, .vs v => .vs (gVarₛ (mkEConₛ Γₛ Γₚ) v)

#check eVarₛ
#check eTmₛ

/-- Given `Γₛ ⊢ Self a₁ a₂ a₃ : U` returns `guard(Γₛ) ⊢ SelfG a₁ a₂ a₃ : SelfE -> U`.

  Challange is that we don't know which type (`Even`, `Odd`, etc) `t` refers to,
  it could be `Even @ 123` or `Odd @ 123`.
  So the output term's type needs to depend on `t`.  -/
def gTmₛ : {Γₛ : Conₛ} -> (γₛE : EConₛA.{u, u+1} Γₛ) ->
  -- (t : Tmₛ Γₛ Aₛ) -> Tmₛ (gConₛ Γₛ γₛE) (gTyₛ Aₛ aₛE)
  (t : Tmₛ Γₛ Aₛ) -> Tmₛ (gConₛ Γₛ γₛE) (gTyₛ Aₛ (TmₛA (eTmₛ t) γₛE))
| Γₛ, γₛE, .var v              => .var (gVarₛ γₛE v)
| Γₛ, γₛE, .app (A := _Aₛ) t u => .app (gTmₛ γₛE t) (.up u)

/-- For example maps the `Vec.cons` ctor of type
```
Vec : Nat ->          U ⊢ (n:Nat) -> (_:A) -> (_ : Vec n) ->            Vec (n+1)
```
into `VecG.cons` of type
```
VecG : Nat -> VecE -> U ⊢ (n:Nat) -> (x:A) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons (n+1) x e)
``` -/
def gTyₚ (γₛE : ConₛA.{u, u+1} (eConₛ Γₛ)) : (A : Tyₚ Γₛ) -> (aE : TyₚA.{u, u+1} (eTyₚ A) γₛE) ->
  Tyₚ (gConₛ Γₛ γₛE)
| El         Self, aE => El (.app (gTmₛ γₛE Self) aE) -- VecG ... (VecE.cons ...)
| PPi   T    Rest, aE => PPi (ULift.{u+1} T) (fun t => gTyₚ γₛE (Rest t.down) (aE t.down))
| PFunc Self Rest, aE => -- this `Self` could be from a different ind type from the mutual block!
    PPi (TmₛA (eTmₛ Self) γₛE) fun e =>  -- (e : SelfE) ->
      PFunc (.app (gTmₛ γₛE Self) e) <| -- SelfG e ->
        gTyₚ γₛE Rest (aE e)

def gConₚ.{u} {Γₛ : Conₛ.{u}} (γₛE : ConₛA.{u, u+1} (eConₛ Γₛ))
  : (Γ : Conₚ.{u} Γₛ) ->
    (γE : ConₚA.{u, u+1} (eConₚ Γ) γₛE) ->
    Conₚ.{u+1} (gConₛ.{_} Γₛ γₛE)
| ⬝, ⟨⟩ => ⬝
| Γ ▹ A, ⟨γE, aE⟩ => gConₚ γₛE Γ γE ▹ gTyₚ γₛE A aE

/-- Cast `"Vec.cons"` to `"VecG.cons"`, similar to `guardTmₚ`. -/
def gVarₚ : {Γ : Conₚ Γₛ} -> (γₛE : ConₛA.{u,u+1} (eConₛ Γₛ)) -> (γE : ConₚA.{u,u+1} (eConₚ Γ) γₛE) ->
  (v : Varₚ Γ A) ->
  Varₚ (gConₚ γₛE Γ γE) (gTyₚ γₛE A (VarₚA (eVarₚ v) γE))
| _ ▹ _, _  ,       _, .vz   => .vz
| _ ▹ _, γₛE, ⟨γE, _⟩, .vs v => .vs (gVarₚ γₛE γE v)

/-- Given `"Vec.cons n x v" : "Vec n"`, we change it to `"VecG.cons n x v vG" : "VecG n (VecE.cons n x v)"`.
  Here, note that we construct `"vG" : "VecG n v"`; in general for every inductive argument. -/
def gTmₚ (γₛE : ConₛA.{u,u+1} (eConₛ Γₛ)) (γE : ConₚA.{u,u+1} (eConₚ Γ) γₛE)
  : (tm : Tmₚ.{u, v} Γ A) ->
    Tmₚ.{u+1, v} (gConₚ γₛE Γ γE) (gTyₚ γₛE A (TmₚA (eTmₚ tm) γE))
| Tmₚ.var v => .var (gVarₚ γₛE γE v)
| Tmₚ.app (A := _A) t u => .app (gTmₚ γₛE γE t) (.up u)
| Tmₚ.appr t u =>
  let e := TmₚA (eTmₚ u) γE
  let g := gTmₚ γₛE γE u
  .appr (.app (gTmₚ γₛE γE t) e) g

set_option pp.universes true in
abbrev GTyₛA.{u, v} (Aₛ : Tyₛ.{u}) (aₛE : TyₛA.{u, u + 1} (eTyₛ.{u} Aₛ)) : Type ((max (u + 1) v) + 1)
  := TyₛA.{u+1, v} (gTyₛ Aₛ aₛE)

abbrev GConₛA.{u, v} (Γₛ : Conₛ.{u}) (γₛE : EConₛA.{u, u+1} Γₛ) : Type ((max (u+1) v) + 1)
  := ConₛA.{u+1, max (u+1) v} (gConₛ.{u} Γₛ γₛE)

abbrev GTmₛ (Γₛ : Conₛ) (Aₛ : Tyₛ) (γₛE : EConₛA.{u,u+1} Γₛ) (aₛE : TyₛA (eTyₛ Aₛ)) : Type (u+2)
  := Tmₛ.{u+1} (gConₛ Γₛ γₛE) (gTyₛ Aₛ aₛE)

abbrev GTmₛA (T : Tmₛ Γₛ Aₛ) (γₛE : EConₛA.{u, u+1} Γₛ) (γₛG : GConₛA.{u, u+1} Γₛ γₛE) : GTyₛA Aₛ (ETmₛA T γₛE)
  := TmₛA (gTmₛ γₛE T) γₛG

abbrev GTyₚ (Γₛ : Conₛ) (γₛE : EConₛA.{u,u+1} Γₛ) : Type (u+2)
  := Tyₚ (gConₛ Γₛ γₛE)

abbrev GTyₚA (A : Tyₚ Γₛ) (γₛE : EConₛA Γₛ) (γₛG : GConₛA Γₛ γₛE) (aE : TyₚA (eTyₚ A) γₛE) : Type _
  := TyₚA (gTyₚ γₛE A aE) γₛG

abbrev GConₚA (Γ : Conₚ Γₛ) (γₛE : EConₛA Γₛ) (γₛG : GConₛA Γₛ γₛE) (γₚE : ConₚA (eConₚ Γ) γₛE) : Type _
  := ConₚA (gConₚ γₛE Γ γₚE) γₛG

abbrev GTmₚ (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) (γₛE : EConₛA.{u,u+1} Γₛ) (γₚE : EConₚA.{u,u+1} Γ γₛE) (tE : ETmₚ.{u, v} Γ A)
  : Type ((max (u+1) v) + 1)
  := Tmₚ.{u+1, v} (gConₚ γₛE Γ γₚE) (gTyₚ γₛE A (TmₚA tE γₚE))

def mkGTyₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₛ : Tyₛ} (t : Tmₛ Ωₛ Aₛ) : TyₛA.{_, _} (gTyₛ Aₛ (mkETyₛ Ωₛ Ωₚ t))
  := mkTyₛ
    (gConₛ Ωₛ (mkEConₛ Ωₛ Ωₚ))
    (gConₚ (mkEConₛ Ωₛ Ωₚ) Ωₚ (mkEConₚ Ωₛ Ωₚ))
    (mkEConₛ_coherent ▸ gTmₛ (mkEConₛ Ωₛ Ωₚ) t) -- unhappy that we need a cast here...

def mkGConₛ.{u} (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) : ConₛA (gConₛ Ωₛ (mkEConₛ Ωₛ Ωₚ))
  := mkConₛ.{u+1, u} (gConₛ Ωₛ (mkEConₛ Ωₛ Ωₚ)) (gConₚ (mkEConₛ Ωₛ Ωₚ) Ωₚ (mkEConₚ Ωₛ Ωₚ))

def mkGTyₚ.{u} (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₚ : Tyₚ Ωₛ} (t : Tmₚ Ωₚ Aₚ)
  := mkTyₚ.{u+1, u}
    (gConₛ Ωₛ (mkEConₛ Ωₛ Ωₚ))
    (gConₚ (mkEConₛ Ωₛ Ωₚ) Ωₚ (mkEConₚ Ωₛ Ωₚ))
    (gTmₚ (mkEConₛ Ωₛ Ωₚ) (mkEConₚ Ωₛ Ωₚ) t)

def mkGConₚ.{u} (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ)
  := mkConₚ.{u+1, u} (gConₛ Ωₛ (mkEConₛ Ωₛ Ωₚ)) (gConₚ (mkEConₛ Ωₛ Ωₚ) Ωₚ (mkEConₚ Ωₛ Ωₚ))

/-
  # Lowering

  We can't determine a single lowered context, and instead have the E and G contexts.
  This makes sense, since we actually have two inductive types E and G.
  We still want to pretend that there is an inductive type L := Σ E G, with its own eliminator.

  ## Lowering Sorts
-/

-- abbrev LTyₛA (Aₛ : Tyₛ.{u})                          : Type (u+2) := (aₛE : ETyₛA.{u,u+1} Aₛ) × GTyₛA.{u,u} Aₛ aₛE
-- abbrev LConₛA (Γₛ : Conₛ)                            : Type (u+2) := (γₛE : EConₛA.{u,u+1} Γₛ) × GConₛA.{u+1, u} Γₛ γₛE
-- abbrev LTmₛ (Γₛ : Conₛ) (Aₛ : Tyₛ) (γₛE : EConₛA Γₛ) : Type (u+2) := (tE  : ETmₛ Γₛ)   × GTmₛ Γₛ Aₛ γₛE tE
-- abbrev LTmₛA {Γₛ : Conₛ} (T : Tmₛ.{u} Γₛ U) (γₛL : LConₛA Γₛ) : Type (u+1) := -- make this `... -> Type (max (u+1) v)` some day.
--   (e : ETmₛA T γₛL.fst) × GTmₛA T γₛL.fst γₛL.snd e

def mkLTyₛ' : (Aₛ : Tyₛ) -> (aₛE : ETyₛA.{u} Aₛ) -> GTyₛA.{u, u+2} Aₛ aₛE -> TyₛA.{u, u+2} Aₛ
| U       , E, G => (e : E) × G e
| SPi X Aₛ, E, G => fun (x : X) => mkLTyₛ' (Aₛ x) E (G (.up x))

/-- Exactly same signature as `mkTyₛ` (other than two more universes), except produces pair of E and G. -/
def mkLTyₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₛ : Tyₛ} (t : Tmₛ Ωₛ Aₛ) : TyₛA.{u, u+2} Aₛ
  := mkLTyₛ' Aₛ (mkETyₛ.{u} Ωₛ Ωₚ t) (mkGTyₛ.{u,u} Ωₛ Ωₚ t)

#check mkConₛ
-- def mkLConₛ := hard to define...
def mkLConₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) : ConₛA Ωₛ :=
  sorry

-- ## Lowering Points
-- def mkLTyₚ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {A : Tyₚ Ωₛ} (t : Tmₚ Ωₚ A) : TyₚA A (mkLConₛ ...) := ...

namespace Example
  universe u v

  -- T
  def Vₛ : Conₛ.{u} := ⬝ ▹ SPi (ULift Nat) (fun _ => U)
  def Vₚ_nil : Tyₚ.{u} Vₛ := El (.app (.var .vz) (.up 0))
  def Vₚ_cons {A : Type u} : Tyₚ Vₛ :=
    PPi (ULift Nat) fun n => -- (n : Nat) ->
      PPi A fun _ => -- A ->
        PFunc (.app (Tmₛ.var vz) n) <| -- Vec n ->
          El (.app (Tmₛ.var vz) (.up <| (ULift.down n) + 1)) -- Vec (n + 1)
  def Vₚ (A : Type u) : Conₚ Vₛ := (⬝ ▹ Vₚ_nil) ▹ @Vₚ_cons A

  -- E
  -- def VₛE : Conₛ     := eConₛ Vₛ
  -- def VₚE : Conₚ VₛE := eConₚ (Vₚ (ULift String))
  -- def VₛEA : EConₛA.{u, u+1} Vₛ.{u}                   := mkConₛ.{u,u} VₛE VₚE
  -- def VₚEA : EConₚA.{u, u+1} (Vₚ (ULift String)) VₛEA := mkConₚ.{u,u} VₛE VₚE
  -- def VecE : ETyₛA.{u, u+1} (SPi (ULift Nat) (fun _ => U)) := mkTyₛ.{u,u} VₛE VₚE (.var .vz)
  def VecE : ETyₛA.{u, u+1} (SPi (ULift Nat) (fun _ => U)) := mkETyₛ.{u} Vₛ (Vₚ (ULift String)) (.var .vz)
  def VecE.nil  := mkETyₚ Vₛ (Vₚ (ULift String)) (.var (.vs .vz))
  def VecE.cons := mkETyₚ Vₛ (Vₚ (ULift String)) (.var .vz)

  -- G
  -- def VₛG : Conₛ     := gConₛ.{u} Vₛ VₛEA
  -- def VₚG : Conₚ VₛG := gConₚ VₛEA (Vₚ (ULift String)) VₚEA
  -- def VₛGA : ConₛA.{u+1, u+2} VₛG      := mkConₛ.{u+1, u} VₛG VₚG
  -- def VₚGA : ConₚA.{u+1, u+2} VₚG VₛGA := mkConₚ.{u+1, u} VₛG VₚG
  -- def VecG := mkTyₛ.{u+1, u} VₛG VₚG (.var .vz)
  def VecG      := mkGTyₛ.{u, u} Vₛ (Vₚ (ULift String)) (.var .vz)
  def VecG.nil  := mkGTyₚ Vₛ (Vₚ (ULift String)) (.var (.vs .vz))
  def VecG.cons := mkGTyₚ Vₛ (Vₚ (ULift String)) (.var .vz)

  -- L
  def VecL' : TyₛA (SPi (ULift Nat) fun _ => U) := mkLTyₛ Vₛ (Vₚ (ULift String)) (.var .vz)
  def VecL : Nat -> Type (u+2) := fun n => (e : VecE) × VecG (.up (.up n)) e
  def VecL.nil : VecL 0 := ⟨.nil, .nil⟩
  def VecL.cons : (n : Nat) -> String -> VecL n -> VecL (n+1)
    := fun n x v => ⟨.cons (.up n) (.up x) v.fst, .cons (.up (.up n)) (.up (.up x)) v.fst v.snd⟩

  #check Vec
  def _Vec  : ULift Nat ->                  Type (u+1) := mkTyₛ.{u, u} Vₛ (Vₚ (ULift String)) (.var .vz)
  def _VecE :                               Type (u+1) := mkETyₛ.{u}   Vₛ (Vₚ (ULift String)) (.var .vz)
  def _VecG : ULift (ULift Nat) -> _VecE -> Type (u+2) := mkGTyₛ.{u, u}   Vₛ (Vₚ (ULift String)) (.var .vz)
  def _VecL : Nat ->                        Type (u+2) := fun n => (e : VecE) × VecG (.up (.up n)) e
end Example

/-
  ## Lowering Terms
  This is done via good old Lean metaprogramming.
-/

open Lean Elab Term Meta
-- open Qq

def lowerDef (e : Expr) : MetaM Expr := do sorry

def lowerInduct (e : Expr) : MetaM Expr := do
  let Γₛ : Expr := sorry
  let Γₚ : Expr := sorry

  sorry
  -- let ΓₚE : Q(Conₚ $ΓₛE) := mkApp2 q(@eConₚ.{0}) Γₛ Γₚ
  -- let γₛE : Q(EConₛA.{0,0} $Γₛ)      := mkApp2 q(@mkConₛ.{0}) ΓₛE ΓₚE
  -- let γₚE : Q(EConₚA.{0,0} $Γₚ $γₛE) := mkApp2 q(@mkConₚ.{0}) ΓₛE ΓₚE

  -- let ΓₛG : Q(Conₛ.{0}) := mkApp2 q(@gConₛ.{0}) Γₛ γₛE
  -- let ΓₚG : Q(Conₚ $ΓₛG) := mkApp4 q(@gConₚ) Γₛ γₛE Γₚ γₚE
  -- let γₛG /- : Q(GConₛA.{0,0} ..) -/ := mkApp2 q(@mkConₛ.{0}) ΓₛG ΓₚG
  -- let γₚG /- : Q(GConₚA.{0,0} ..)-/ := mkApp2 q(@mkConₚ.{0}) ΓₛG ΓₚG
  -- -- let L : Q(Type) := q(@Sigma )
-- #exit

/-- Given `Vec 123`, produces `VecL 123`. -/
def lowerTmₛ (e : Expr) : MetaM Expr := do
  sorry

/-- Given `Vec.cons`, produces `VecL.cons`. -/
def lowerTyₚ (e : Expr) : MetaM Expr := do
  sorry

/-- Lowers a term.  -/
def lowerTm (e : Expr) : MetaM Expr := do
  match e with
  | .app f a =>
    -- `⊢ f : Pi A B`
    -- `⊢ a : A`
    -- `f a : B[a]`
    -- `⊢ fᴸ : Pi Aᴸ Bᴸ`
    return .app (<- lowerTm f) (<- lowerTm a)
  -- | .lam .. => sorry
  | .const name _ =>
    match <- getConstInfo name with
    | .inductInfo _ => lowerInduct e
    | .ctorInfo _ => lowerTyₚ e
    | .defnInfo _ => lowerDef e
    | _ => throwError "lowerEnv: unsupported const kind for {name}"
  | _ => throwError "oh no, lowerTm {e}"

/-- Lowers a type. `lower : Ty Γ -> Ty Γᴸ`
```
def lowerTy : {Γ : Con} -> Ty Γ -> Ty Γᴸ
| Γ, .Pi A B => -- where `Ty.Pi : (A : Ty Γ) -> Ty (Γ, A) -> Ty Γ`
  let AL : Ty Γᴸ := lowerTy A
  let BL : Ty (Γᴸ, Aᴸ) := lowerTy B -- because `(Γ, A)ᴸ ≣ (Γᴸ, Aᴸ)`
  .Pi AL BL -- typechecks
| Γ, El T => sorry
``` -/
partial def lowerTy (u : Level) (e : Expr) : MetaM Expr := do
  if let Expr.sort _ := e then -- case `U : Ty Γ`
    return e
  else if let .forallE _ A _ _ := e then -- case `Pi A B : Ty Γ`
    Meta.forallBoundedTelescope e (some 1) fun a_fv B => do
      let Γ_A <- getLCtx -- `Γ, A` and `Γ, A ⊢ B`
      let AL : Expr <- lowerTy u A -- Γᴸ ⊢ Aᴸ
      let BL : Expr <- lowerTy u B -- (Γ, A)ᴸ ⊢ Bᴸ    is (hopefully) well-typed again.
      let Γ_AL := Γ_A.modifyLocalDecl a_fv[0]!.fvarId! (fun ldecl => ldecl.setType AL)
      withLCtx Γ_AL (<- getLocalInstances) do
        mkForallFVars a_fv BL
  else if let .fvar fv := e then
    -- `⊢ a : A` gets casted to `⊢ aL : Aᴸ`. Since metaprogramming is untyped, this is a no-op.
    return .fvar fv
  else -- case `El T : Ty Γ`
    lowerTm e
    -- let T := e.getAppFn
    -- let args := e.getAppArgs
    -- let v <- mkFreshLevelMVar
    -- if <- isDefEq T (.const ``Vec [v]) then
    --   let n := args[1]!
    --   return mkAppN (.const ``Sigma [u, u]) #[.const ``Example.VecE [u], .app (.const ``Example.VecG [u]) n]
    -- else if T.isAppOf ``Eq then return mkAppN (.const ``Eq [.zero]) args
    -- else if T.isAppOf ``Nat || T.isAppOf ``String then return e
    -- else throwError "oh no, {e}"

-- open Example
@[irreducible] def len  : Vec String n -> Nat := fun _ => n

elab "lower! " T:term : term => do
  let T <- elabTerm T none
  let u <- Meta.mkFreshLevelMVar
  lowerTy (u := u) T

#check ∀n, ∀x, lower! ∀v, len (Vec.cons n x v) = (len v) + 1
/- (n : Nat) → (x : String) → (v : PSigma (VecG n)) → TEq (len (Vec.cons n x v)) (len v + 1) -/

-- #eval lowerTy q((v : MutualInductive.Vec String (nat_lit 0)) -> TEq (len (Vec.cons 0 "a" v)) ((len v) + 1))



#exit

-- /-- For example maps `"Vec 123"` to `⟨"VecE", "VecG 123"⟩`. -/
-- def lTmₛ {Γₛ : Conₛ} {Aₛ : Tyₛ} (γₛE : ConₛA (eConₛ Γₛ)) (t : Tmₛ Γₛ Aₛ) : LTmₛ Γₛ Aₛ γₛE
--   := ⟨eTmₛ t, gTmₛ γₛE t⟩

-- /-- We want to obtain the actual `(e : VecE) × VecG e`. -/
-- def lTmₛA (γₛE : ConₛA (eConₛ Γₛ)) (γₛG : ConₛA (gConₛ Γₛ γₛE)) (T : Tmₛ Γₛ U) : Type _
--   := @Sigma (ETmₛA T γₛE) (GTmₛA T γₛE γₛG)


-- /-- Construct new inductive types. -/
-- def mkLConₛ : (Γₛ : Conₛ) -> (Γₚ : Conₚ Γₛ) -> ConₛA.{0,0} Γₛ
-- | Γₛ, Γₚ =>
--   let γₛE := mkEConₛ Γₛ Γₚ
--   let γₛG := mkGConₛ Γₛ Γₚ
--   @Sigma γₛE


-- abbrev LTyₚA (A : Tyₚ Γₛ) (γₛL : LConₛA Γₛ) : Type _ := (e : ETyₚA A γₛL.fst) × GTyₚA A γₛL.fst γₛL.snd e
-- abbrev LConₚA (Γ : Conₚ Γₛ) (γₛL : LConₛA Γₛ) : Type _ := (e : EConₚA Γ γₛL.fst) × GConₚA Γ γₛL.fst γₛL.snd e
-- abbrev LTmₚ {Γₛ : Conₛ} (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) (γₛE) (γₚE : ConₚA (eConₚ Γ) γₛE) : Type _
--   := (tE : ETmₚ Γ A) × GTmₚ Γ A γₛE γₚE tE

-- /-- Given a term `"Vec.cons n x v"`, produce
--   `⟨"VecE.cons n x vᴱ", "VecG.cons n x vᴱ vᴳ"⟩ : Tmₛ ["VecE"] "U" × Tmₛ ["VecG"] "VecE -> U"`. -/
-- def lTmₚ {Γₛ : Conₛ} {Γ : Conₚ Γₛ} {A : Tyₚ Γₛ} {γₛE} {γₚE : ConₚA (eConₚ Γ) γₛE}
--   (t : Tmₚ Γ A) : LTmₚ Γ A γₛE γₚE
--   := ⟨eTmₚ t, gTmₚ γₛE γₚE t⟩

-- /-- Given `"Vec.cons ..." : "Vec 123"`, produce `⟨VecE.cons ..., VecG.cons ...⟩ : @Sigma VecE (VecG 123)`. -/
-- def lTmₚA (γₛE : ConₛA (eConₛ Γₛ)) (γₛG : ConₛA (gConₛ Γₛ γₛE))
--   (γE : ConₚA (eConₚ Γ) γₛE) (γG : ConₚA (gConₚ γₛE Γ γE) γₛG)
--   (t : Tmₚ Γ (El T))
--   : lTmₛA γₛE γₛG T
--   := by
--     let g := TmₚA (gTmₚ γₛE γE t) γG
--     rw [gTyₚ] at g
--     rw [TyₚA] at g
--     rw [TmₛA] at g
--     exact ⟨TmₚA (eTmₚ t) γE, g⟩

-- section
--   open Example
--   -- Sorts
--   example : LConₛA Vₛ = ((γₛE : PUnit.{2} × Type) × (PUnit.{2} × (Nat → γₛE.snd → Type))) := rfl
--   example : LConₛA Vₛ := ⟨⟨⟨⟩, VecE⟩, ⟨⟨⟩, VecG⟩⟩
--   /-- `"Vec 123" : "U"` becomes `⟨"VecE", "VecG 123"⟩ : "U" × "VecE -> U"` -/
--   example : lTmₛ  (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩            (.app (.var .vz) 123) = ⟨.var .vz, .app (.var .vz) 123⟩ := rfl
--   example : lTmₛA (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩ (.app (.var .vz) 123) = @Sigma VecE (VecG 123)          := rfl

--   -- Points
--   example : lTmₚA (Γₛ := Vₛ) (Γ := V String)
--     ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
--     (.var (.vs .vz))
--     = ⟨VecE.nil, VecG.nil⟩ := rfl
--   example : lTmₚA (Γₛ := Vₛ) (Γ := V String)
--     ⟨⟨⟩, VecE⟩                  ⟨⟨⟩, VecG⟩
--     ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
--     (
--       let asdf1 : Tmₚ (V String) (PPi String fun _x => PFunc (.app (Tmₛ.var vz) 0) (El _)) := .app (.var .vz) 0
--       let asdf2 : Tmₚ (V String) (                     PFunc (.app (Tmₛ.var vz) 0) (El _)) := .app asdf1 "" -- ! if you inline `asdf1` it breaks
--       let asdf3 : Tmₚ (V String) (                                                 (El _)) := .appr asdf2 (.var (.vs .vz))
--       asdf3 -- ! if you inline asdf3 is breaks as well
--     )
--     = ⟨VecE.cons 0 "" VecE.nil, VecG.cons 0 "" VecE.nil VecG.nil⟩
--     := rfl
-- end



-- #exit

/- # Reconstruction for Mutually Inductive Types
  Given `P : Vec n -> Prop`, We can derive `P' : @Sigma VecE (VecG n) -> Prop`.
  And now given `prf' : P' ⟨vE, vG⟩`, we need to find `?prf : P v`.

  So originally we had goal `v : Vec n ⊢ ?prf : P v`.
  We have a `down : Vec n -> Sigma VecE (VecG n)` function, such that `down ∘ up = id`. // down is `lower`
  We derive `P' : Sigma VecE (VecG n) -> Prop`, such that `P' (down v) -> P v`. !!! how "such that"? This is the crucial part.
-/

-- -- This is just `rTyₛA {Aₛ} _ ≣ TyₛA Aₛ` ?
-- def rTyₛA : {Aₛ : Tyₛ} -> LTyₛA.{0,0,0} Aₛ -> TyₛA Aₛ
-- | U      , _      => Type
-- | SPi X _, ⟨E, G⟩ => fun (x : X) => rTyₛA ⟨E, G x⟩

-- def rConₛA : {Γₛ : Conₛ} -> LConₛA Γₛ -> ConₛA Γₛ
-- | ⬝    , ⟨⟨⟩, ⟨⟩⟩ => ⟨⟩
-- | _ ▹ _, ⟨⟨γE, aE⟩, ⟨γG, aG⟩⟩ => ⟨rConₛA ⟨γE, γG⟩, rTyₛA ⟨aE, aG⟩⟩

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
  set_option linter.unusedVariables false in
  /-- You can specify an eliminator for VecL, which behaves exactly the way that Vec.rec does. -/
  noncomputable def VecL.elim
    {motive : (n : Nat) -> VecL n -> Sort u}
    (nilD : motive 0 nilL)
    (consD : (n : Nat) -> (x : String) -> (vL : VecL n) -> motive n vL -> motive (n + 1) (.cons n x vL))
    (n : Nat)
    (vL : VecL n)
    : motive n vL :=
    VecE.rec (fun vE => (vG : VecG n vE) -> motive n ⟨vE, vG⟩)
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


#exit

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

open Lean Elab Term Meta
open Qq
open Example

abbrev Ty (_Γ : LocalContext) : Type := Q(Type)
abbrev lowerCon : LocalContext -> LocalContext := id

def lowerEnvDef (e : Expr) : MetaM Expr := do sorry

structure Ind where
  Γₛ : Q(Conₛ.{0})
  Γₚ : Q(Conₚ $Γₛ)
-- def Ind.E (i : Ind) : Ind := { }

/-- Given `Vec`, produces `VecL`. -/
def lowerTyₛ (e : Expr) : MetaM Expr := do
  let Γₛ : Q(Conₛ.{0}) := sorry
  let Γₚ : Q(Conₚ $Γₛ) := sorry

  let ΓₛE : Q(Conₛ.{0}) := mkApp  q(@eConₛ.{0}) Γₛ
  let ΓₚE : Q(Conₚ $ΓₛE) := mkApp2 q(@eConₚ.{0}) Γₛ Γₚ
  let γₛE : Q(EConₛA.{0,0} $Γₛ)      := mkApp2 q(@mkConₛ.{0}) ΓₛE ΓₚE
  let γₚE : Q(EConₚA.{0,0} $Γₚ $γₛE) := mkApp2 q(@mkConₚ.{0}) ΓₛE ΓₚE

  let ΓₛG : Q(Conₛ.{0}) := mkApp2 q(@gConₛ.{0}) Γₛ γₛE
  let ΓₚG : Q(Conₚ $ΓₛG) := mkApp4 q(@gConₚ) Γₛ γₛE Γₚ γₚE
  let γₛG /- : Q(GConₛA.{0,0} ..) -/ := mkApp2 q(@mkConₛ.{0}) ΓₛG ΓₚG
  let γₚG /- : Q(GConₚA.{0,0} ..)-/ := mkApp2 q(@mkConₚ.{0}) ΓₛG ΓₚG
  let L : Q(Type) := q(@Sigma $)
  sorry

/-- Given `Vec.cons`, produces `VecL.cons`. -/
def lowerTyₚ (e : Expr) : MetaM Expr := do
  sorry

def lowerEnv (e : Expr) : MetaM Expr := do
  let .const name _ := e | throwError "lowerEnv: not a const"
  match <- getConstInfo name with
  | .inductInfo _ => lowerTyₛ e
  | .ctorInfo _ => lowerTyₚ e
  | .defnInfo di => sorry
  | _ => throwError "lowerEnv: unsupported const kind for {name}"

/-- Lowers a term.  -/
def lowerTm (e : Expr) : MetaM Expr := do
  match e with
  | .app f a =>
    -- `⊢ f : Pi A B`
    -- `⊢ a : A`
    -- `f a : B[a]`
    -- `⊢ fᴸ : Pi Aᴸ Bᴸ`
    return .app (<- lowerTm f) (<- lowerTm a)
  -- | .lam .. => sorry
  | .const name lvls => lowerEnv name lvls
  | _ => throwError "oh no, lowerTm {e}"

/-- Lowers a type. `lower : Ty Γ -> Ty Γᴸ`
```
def lowerTy : {Γ : Con} -> Ty Γ -> Ty Γᴸ
| Γ, .Pi A B => -- where `Ty.Pi : (A : Ty Γ) -> Ty (Γ, A) -> Ty Γ`
  let AL : Ty Γᴸ := lowerTy A
  let BL : Ty (Γᴸ, Aᴸ) := lowerTy B -- because `(Γ, A)ᴸ ≣ (Γᴸ, Aᴸ)`
  .Pi AL BL -- typechecks
| Γ, El T => sorry
``` -/
partial def lowerTy (u : Level) (e : Expr) : MetaM Expr := do
  if let Expr.sort _ := e then -- case `U : Ty Γ`
    return e
  else if let .forallE _ A _ _ := e then -- case `Pi A B : Ty Γ`
    Meta.forallBoundedTelescope e (some 1) fun a_fv B => do
      let Γ_A <- getLCtx -- `Γ, A` and `Γ, A ⊢ B`
      let AL : Expr <- lowerTy u A -- Γᴸ ⊢ Aᴸ
      let BL : Expr <- lowerTy u B -- (Γ, A)ᴸ ⊢ Bᴸ    is (hopefully) well-typed again.
      let Γ_AL := Γ_A.modifyLocalDecl a_fv[0]!.fvarId! (fun ldecl => ldecl.setType AL)
      withLCtx Γ_AL (<- getLocalInstances) do
        mkForallFVars a_fv BL
  else if let .fvar fv := e then
    -- `⊢ a : A` gets casted to `⊢ aL : Aᴸ`. Since metaprogramming is untyped, this is a no-op.
    return .fvar fv
  else -- case `El T : Ty Γ`
    let T := e.getAppFn
    let args := e.getAppArgs
    let v <- mkFreshLevelMVar
    if <- isDefEq T q(Vec.{v}) then
      let n := args[1]!
      return mkAppN (.const ``Sigma [u, u]) #[q(VecE.{u}), .app q(VecG.{u}) n]
    else if T.isAppOf ``Eq then return mkAppN (.const ``Eq [.zero]) args
    else if T.isAppOf ``Nat || T.isAppOf ``String then return e
    else throwError "oh no, {e}"

#check Sigma
#check Vec
#check VecE
#check VecG

elab "lower! " T:term : term => do
  let T <- elabTerm T none
  let u <- Meta.mkFreshLevelMVar
  lowerTy (u := u) T

#check ∀n, ∀x, lower! ∀v, len (Vec.cons n x v) = (len v) + 1
/- (n : Nat) → (x : String) → (v : PSigma (VecG n)) → TEq (len (Vec.cons n x v)) (len v + 1) -/

#eval lowerTy q((v : MutualInductive.Vec String (nat_lit 0)) -> TEq (len (Vec.cons 0 "a" v)) ((len v) + 1))
