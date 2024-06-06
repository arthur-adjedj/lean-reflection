import Reflection.MInd
import Reflection.IndexErasure.Erase

namespace Reflection.IndexErasure

set_option pp.fieldNotation.generalized false
open Reflection MInd
open Tyₛ Tyₚ Varₛ Varₚ

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
