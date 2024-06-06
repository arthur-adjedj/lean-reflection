import Reflection.MInd
import Reflection.IndexErasure.Erase
import Reflection.IndexErasure.Guard

namespace Reflection.IndexErasure

set_option pp.fieldNotation.generalized false
open Reflection MInd
open Tyₛ Tyₚ Varₛ Varₚ

/-
  # Lowering

  We can't determine a single lowered context, and instead have the E and G contexts.
  This makes sense, since we actually have two inductive types E and G.
  We still want to pretend that there is an inductive type L := Σ E G, with its own eliminator.
-/

/-
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


/-
  ## Lowering Points
-/

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
