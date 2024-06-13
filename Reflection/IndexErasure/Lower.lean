import Reflection.MInd
import Reflection.IndexErasure.Erase
import Reflection.IndexErasure.Guard

namespace Reflection.IndexErasure

open Reflection MInd
open Tyₛ Tyₚ Varₛ Varₚ

set_option pp.proofs true
set_option pp.fieldNotation.generalized false

/-
  # Lowering

  We can't determine a single lowered context, and instead have the E and G contexts.
  This makes sense, since we actually have two inductive types E and G.
  We still want to pretend that there is an inductive type L := Σ E G, with its own eliminator.
-/

/-
  ## Lowering Sorts
-/

def mkLTyₛ' : (Aₛ : Tyₛ) -> (aₛE : ETyₛA.{u} Aₛ) -> GTyₛA.{u, u+2} Aₛ aₛE -> TyₛA.{u, u+2} Aₛ
| U       , E, G => (e : E) × G e
| SPi X Aₛ, E, G => fun (x : X) => mkLTyₛ' (Aₛ x) E (G (.up x))

/-- Exactly same signature as `mkTyₛ` (other than two more universes), except produces pair of E and G.

  `mkTyₛ` returns something like `fun (n:Nat) => fun y => Tmₚ _ _`.
  And we want `mkLTyₛ` to instead return `fun (n:Nat) => fun y => Tmₚ _ _ × Tmₚ _ _`,
  so the same lambda telescope, but the type it returns is a Σ.
-/
def mkLTyₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₛ : Tyₛ} (t : Tmₛ Ωₛ Aₛ) : TyₛA.{u, u+2} Aₛ
  := mkLTyₛ' Aₛ (mkETyₛ.{u} Ωₛ Ωₚ t) (mkGTyₛ.{u,u} Ωₛ Ωₚ t)

def mkLConₛ' (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Γₛ} : Subₛ.{u} Ωₛ Γₛ -> ConₛA.{u, _} Γₛ
| .nil => ⟨⟩
| .cons σ t => ⟨mkLConₛ' Ωₛ Ωₚ σ, mkLTyₛ Ωₛ Ωₚ t⟩

def mkLConₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) : ConₛA Ωₛ := mkLConₛ' Ωₛ Ωₚ (Subₛ.id Ωₛ)

#reduce mkLConₛ (Vₛ) (Vₚ String)

theorem mkLConₛ_coherent : (t : Tmₛ Γₛ Aₛ) -> (σ : Subₛ Ωₛ Γₛ) -> TmₛA.{u} t (@mkLConₛ'.{u} Ωₛ Ωₚ Γₛ σ) = @mkLTyₛ.{u} Ωₛ Ωₚ Aₛ (SubₛTm t σ)
| t                 , .nil      => False.elim (Tmₛ_emptyCtx t)
| .var .vz          , .cons σ s => rfl
| .var (.vs v)      , .cons σ s => by
  -- have ih : TmₛA (Tmₛ.var v) (mkConₛ' Ωₛ Ωₚ σ) = mkTyₛ Ωₛ Ωₚ (SubₛTm (Tmₛ.var v) σ)
  --   := mkLConₛ_coherent (.var v) σ
  rw [TmₛA_var]
  simp_all only [TmₛA_var, SubₛTm, VarₛA, SubₛVar]
  sorry
  done
| .app (A := Cₛ) f τ, σ => by
  rw [TmₛA_app, mkLConₛ_coherent f σ, SubₛTm]
  simp [mkLTyₛ, mkLTyₛ', mkGTyₛ, gTmₛ]
  congr
  -- easy :3
  sorry
  done


/- ## Lowering Points -/

def mkLTyₚ' (Ωₛ : Conₛ.{u}) (Ωₚ : Conₚ Ωₛ) :
  {A : Tyₚ Ωₛ} ->
  (tE : ETmₚ Ωₚ A) ->
  (tG : GTmₚ Ωₚ A (mkEConₛ Ωₛ Ωₚ) (mkEConₚ Ωₛ Ωₚ) tE) ->
  TyₚA A (mkLConₛ Ωₛ Ωₚ)
| El Self        , tE, tG => by
  rw [TyₚA, mkLConₛ, mkLConₛ_coherent, mkLTyₛ, mkLTyₛ', SubₛTm_id, mkGTyₛ]
  simp only [mkGTyₛ, mkTyₛ]
  rw [GTmₚ, gTyₚ] at tG
  have h {A B : TyₛA U} (tm_f : Tmₛ (gConₛ Ωₛ (mkEConₛ Ωₛ Ωₚ)) (gTyₛ U A))
    (a : A) (b : B) (eq : A = B) (eqq : a = Eq.rec b eq.symm)
    : Tmₛ.app tm_f a = Tmₛ.app (eq ▸ tm_f) b := by cases eq; congr
  have h' := h (gTmₛ (mkEConₛ Ωₛ Ωₚ) Self) (TmₚA tE (mkEConₚ Ωₛ Ωₚ)) tE mkEConₛ_coherent
    (by rw [mkEConₚ, mkConₚ, mkConₚ_coherent, mkTyₚ, SubₚTm_id]; simp only [Eq.mpr, eq_cast_trans])
  rw [h'] at tG
  exact ⟨tE, tG⟩
| PPi X Rest     , tE, tG => fun τ => mkLTyₚ' _ _ (.app tE τ) (.app tG (.up τ))
| PFunc Self Rest, tE, tG => fun self => by
  rw [mkLConₛ, mkLConₛ_coherent, SubₛTm_id, mkLTyₛ, mkLTyₛ'] at self
  let ⟨selfE, selfG⟩ := self

  have h {A B : TyₛA U} (tm_f : Tmₛ (gConₛ Ωₛ (mkEConₛ Ωₛ Ωₚ)) (gTyₛ U A))
    (a : A) (b : B) (eq : A = B) (eqq : a = Eq.rec b eq.symm)
    : Tmₛ.app tm_f a = Tmₛ.app (eq ▸ tm_f) b
    := by cases eq; congr
  have h' := h (gTmₛ (mkEConₛ Ωₛ Ωₚ) Self) (Eq.rec selfE mkEConₛ_coherent.symm) selfE mkEConₛ_coherent rfl

  let tGe
    : Tmₚ (gConₚ (mkEConₛ Ωₛ Ωₚ) Ωₚ (mkEConₚ Ωₛ Ωₚ))
      (PFunc
        (Tmₛ.app (gTmₛ (mkEConₛ Ωₛ Ωₚ) Self) (Eq.rec selfE mkEConₛ_coherent.symm)) -- : Tmₛ (gConₛ Ωₛ (mkEConₛ Ωₛ Ωₚ)) U
        (gTyₚ (mkEConₛ Ωₛ Ωₚ) Rest (TmₚA tE (mkEConₚ Ωₛ Ωₚ) (Eq.rec selfE mkEConₛ_coherent.symm)))
      )
    := Tmₚ.app tG (Eq.rec selfE mkEConₛ_coherent.symm)
  let tGeg := Tmₚ.appr tGe (h' ▸ selfG)

  let exp : Tmₚ
    (gConₚ (mkEConₛ Ωₛ Ωₚ) Ωₚ (mkEConₚ Ωₛ Ωₚ))
    (gTyₚ (mkEConₛ Ωₛ Ωₚ) Rest (TmₚA (Tmₚ.appr tE selfE) (mkEConₚ Ωₛ Ωₚ)))
    := by
      rw [TmₚA]
      rw [mkEConₚ_coherent_bad]
      rw [mkEConₚ_coherent_bad] at tGeg
      -- conv => arg 2; arg 3; arg 3
      have : (mkETyₚ_bad Ωₛ Ωₚ tE (Eq.rec selfE mkEConₛ_coherent.symm)) = (mkETyₚ_bad Ωₛ Ωₚ tE (TmₚA selfE (mkEConₚ Ωₛ Ωₚ)))
        := by
          rw [mkEConₚ, mkConₚ]
          rw [mkConₚ_coherent]
          rw [mkTyₚ]
          simp only [Eq.mpr, SubₚTm_id, eq_cast_trans]
      rw [<- this]
      exact tGeg
  exact mkLTyₚ' _ _ (.appr tE selfE) exp

/-- Define a constructor for the lowered type. -/
def mkLTyₚ (Ωₛ : Conₛ.{u}) (Ωₚ : Conₚ Ωₛ) {A : Tyₚ Ωₛ} (t : Tmₚ Ωₚ A) : TyₚA A (mkLConₛ Ωₛ Ωₚ)
  := mkLTyₚ' Ωₛ Ωₚ (eTmₚ t) (gTmₚ (mkEConₛ Ωₛ Ωₚ) (mkEConₚ Ωₛ Ωₚ) t)

#print axioms mkLTyₚ

def _VecL := mkTyₛ.{0} Vₛ (Vₚ String) (.var .vz)
def _VecL.nil := mkLTyₚ.{0} Vₛ (Vₚ String) (.var (.vs .vz))
def _VecL.cons := mkLTyₚ.{0} Vₛ (Vₚ String) (.var .vz)
#reduce _VecL.nil
#reduce _VecL
-- set_option maxHeartbeats 20000000 -- even 20000000 is not enough lmao
-- #reduce _VecL.cons

#check Nₛ
#check N
#reduce mkLTyₚ.{0} Nₛ N (.var (.vs .vz))
#reduce mkLTyₚ.{0} Nₛ (Conₚ.ext Conₚ.nil (PPi Nat (fun _ => El (.var .vz)))) (.var .vz)
-- #reduce mkLTyₚ.{0} Nₛ N (.var .vz)

#reduce TyₚA V_cons (mkLConₛ Vₛ (Vₚ String))

example :
    _VecL.cons =
    fun (n : Nat) (x : String) (v : TmₛA (Tmₛ.app (Tmₛ.var Varₛ.vz) n) (mkLConₛ Vₛ (Vₚ String))) =>
      ⟨
        Tmₚ.appr (Tmₚ.app (Tmₚ.app (Tmₚ.var Varₚ.vz) (ULift.up n)) x) v.fst,
        Tmₚ.appr (Tmₚ.app (Tmₚ.app (Tmₚ.app (Tmₚ.var Varₚ.vz) n) x) v.fst) v.snd
      ⟩
  := sorry

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

  #reduce VecE.cons

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
