import Reflection.MutualInductive

open Tyₛ Tyₚ Varₛ Varₚ

-- set_option pp.universes true

-- # Erasure

def eraseTyₛ : Tyₛ.{u} -> Tyₛ.{u}
| _ => U

/-- For example maps sort-ctx `[Vec : Nat -> U, ...]` into `[VecE : U, ...]`. -/
def eraseConₛ : Conₛ.{u} -> Conₛ.{u}
| ⬝      => ⬝
| Γₛ ▹ _ => eraseConₛ Γₛ ▹ U

/-- This is a no-op, other than changing the type of the variable. -/
def eraseVarₛ : Varₛ Γₛ Aₛ -> Varₛ (eraseConₛ Γₛ) U
| .vz   => .vz
| .vs v => .vs (eraseVarₛ v)

/-- For example maps `Vec : Nat -> U ⊢ Vec 123 : U` into `VecE : U ⊢ VecE : U`. -/
def eraseTmₛ : Tmₛ Γₛ Aₛ -> Tmₛ (eraseConₛ Γₛ) U
| .var v              => .var (eraseVarₛ v)
| .app (A := _Aₛ) t u => eraseTmₛ t

/-- For example for `Vec.nil`, maps `Vec : Nat -> U ⊢ Vec 0` into `VecE : U ⊢ VecE`,
and for `Vec.cons` maps `Vec : Nat -> U ⊢ (n:Nat) -> α -> Vec n -> Vec (n+1)`
into `VecE : U ⊢ (n:Nat) -> α -> VecE -> VecE`. -/
def eraseTyₚ {Γₛ : Conₛ} : Tyₚ Γₛ -> Tyₚ (eraseConₛ Γₛ)
| El         Self => El (eraseTmₛ Self)
| PPi   T    Rest => PPi T (fun t => eraseTyₚ (Rest t))
| PFunc Self Rest => PFunc (eraseTmₛ Self) (eraseTyₚ Rest)

def eraseConₚ : Conₚ Γₛ -> Conₚ (eraseConₛ Γₛ)
| ⬝ => ⬝
| Γ ▹ A => (eraseConₚ Γ) ▹ (eraseTyₚ A)



-- # Guard


-- /-- For example maps `Vec : Nat -> U` to `VecG : Nat -> VecE -> U`. -/
-- def guardTyₛ' : (Aₛ : Tyₛ.{u}) -> TyₛA.{u, u} (eraseTyₛ Aₛ) -> Tyₛ.{u}
-- | U         , aₛE => SPi aₛE (fun _ => U)
-- | SPi T Rest, aₛE => SPi T   (fun t => guardTyₛ' (Rest t) aₛE)

/-- Given a `Γₛ ⊢ Self a₁ a₂ a₃ : U` (note the type `U`),
  computes the type `SelfE -> U` for `(guard Γₛ) ⊢ SelfG a₁ a₂ a₃ : SelfE -> U`. -/
def guardTyₛ : (Aₛ : Tyₛ) -> (γₛE : ConₛA.{u, u} (eraseConₛ Γₛ)) -> (t : Tmₛ Γₛ Aₛ) -> Tyₛ
| U      , γₛE, tm => SPi (TmₛA (eraseTmₛ tm) γₛE) fun _ => U
| SPi T f, γₛE, tm => SPi T                        fun τ => guardTyₛ (f τ) γₛE (.app tm τ)

-- example : guardTyₛ' Aₛ aₛE = guardTyₛ (Γₛ := Aₛ :: Γₛ) Aₛ ⟨aₛE, γₛE⟩ (.var .vz) := by
--   induction Aₛ with
--   | U =>
--     rw [guardTyₛ, guardTyₛ', eraseTmₛ, eraseVarₛ, TmₛA_var]
--     exact .refl _
--   | SPi T f ih =>
--     rw [guardTyₛ, guardTyₛ']
--     simp
--     apply funext
--     intro a
--     have ih := @ih a aₛE
--     rw [ih]
--     -- on the lhs `.var .vz       : Tmₛ (f a     :: Γₛ) (f a)`
--     -- on the rhs `.var .vz       : Tmₛ (SPi T f :: Γₛ) (SPi T f)`
--     -- on the rhs `(.var .vz) @ a : Tmₛ (SPi T f :: Γₛ) (f a)`

--     -- @Eq Tyₛ
--     --   @guardTyₛ (f a :: Γₛ) (f a) (aₛE, γₛE) (Tmₛ.var Varₛ.vz)
--     --   @guardTyₛ (SPi T f :: Γₛ) (f a) (aₛE, γₛE) (Tmₛ.var Varₛ.vz @ a)

--     done

/-- For example maps sort-stx `[Vec : Nat -> U]` into `[VecG : Nat -> VecE -> U]`. -/
def guardConₛ : (Γₛ : Conₛ) -> (γₛE : ConₛA (eraseConₛ Γₛ)) -> Conₛ
| ⬝      , ⟨⟩         => ⬝
-- | .cons Aₛ Γₛ, ⟨aₛE, γₛE⟩ => .cons (guardTyₛ' Aₛ aₛE) (guardConₛ Γₛ γₛE)
| Γₛ ▹ Aₛ, ⟨γₛE, aₛE⟩ => guardConₛ Γₛ γₛE ▹ guardTyₛ (Γₛ := Γₛ ▹ Aₛ) Aₛ ⟨γₛE, aₛE⟩ (.var .vz)
  -- .cons (guardTyₛ (Γₛ := Γₛ) Aₛ γₛE sorry) (guardConₛ Γₛ γₛE)

#check guardConₛ Vₛ ⟨⟨⟩, List Nat⟩
#reduce guardConₛ Vₛ ⟨⟨⟩, List Nat⟩
#reduce ConₛA (guardConₛ Vₛ ⟨⟨⟩, List Nat⟩)

-- def guardVarₛ : (Γₛ : Conₛ.{max u v}) -> (γₛE : ConₛA (eraseConₛ Γₛ)) -> Varₛ.{max u v} Γₛ Aₛ ->
--   Varₛ.{max u v} (guardConₛ.{u, v} Γₛ γₛE) (guardTyₛ.{u, v} Aₛ aₛE) -- ! problem here aₛE needs to come from γₛE, but doesn't rn
-- | Aₛ :: Γₛ, ⟨aₛE, γₛE⟩, .vz => sorry -- and you actually do have the correct aₛE here...
-- | Bₛ :: Γₛ, ⟨aₛE, γₛE⟩, .vs v => .vs (guardVarₛ Γₛ γₛE v)

-- set_option pp.explicit true
-- set_option pp.funBinderTypes true

-- I don't think this is provable
-- theorem guardTyₛ_step (v : Varₛ Γₛ Aₛ) : (Aₛ : Tyₛ) -> (tm : Tmₛ Γₛ Aₛ) -> guardTyₛ Aₛ γₛE tm = @guardTyₛ (Bₛ :: Γₛ) Aₛ (bₛE, γₛE) (vshift tm)
-- | U, tm => by
--     simp [guardTyₛ, TmₛA, eraseTmₛ, vshift]
--     done
-- | SPi T f, tm => sorry

theorem guardTyₛ_step (v : Varₛ Γₛ Aₛ) : guardTyₛ Aₛ γₛE (.var v) = @guardTyₛ (Γₛ ▹ Bₛ) Aₛ (γₛE, bₛE) (.var (.vs v)) := by
  induction Aₛ with
  | U =>
    -- most scuffed proof
    simp [guardTyₛ]
    simp [eraseTmₛ]
    simp [VarₛA]
    rw [TmₛA_var]
    rw [TmₛA_var]
    exact .refl _
  | SPi T f ih =>
    rw [guardTyₛ]
    rw [guardTyₛ]
    simp [guardTyₛ]
    apply funext
    intro x
    -- exact ih x (v)
    sorry
    done

#check vshift

-- def stepUp :
--   (v : Varₛ Γₛ Aₛ) ->
--     Varₛ (guardTyₛ (Γₛ := Aₛ :: Γₛ) Aₛ ⟨aₛE, γₛE⟩ (.var .vz) :: guardConₛ Γₛ γₛE) (guardTyₛ (Γₛ :=       Γₛ) Aₛ       γₛE  (.var      v )) ->
--     -- Varₛ (guardConₛ (Bₛ :: Γₛ) (bₛE, γₛE)) (guardTyₛ (Γₛ :=       Γₛ) Aₛ       γₛE  (.var      v )) ->
--     Varₛ (guardConₛ (Bₛ :: Γₛ) (bₛE, γₛE)) (guardTyₛ (Γₛ := Bₛ :: Γₛ) Aₛ (bₛE, γₛE) (.var (.vs v)))
-- | _, .vz => sorry
-- | _, .vs w => sorry

/-- Given a variable `Vec:N->U ⊢ VAR(Vec) : N->U`, we return `VecG:N->VecE->U ⊢ VAR(VecG) : N->VecE->U`.
  The runtime de-brujin value of this variable doesn't change. So this is basically just a cast operator. -/
def guardVarₛ : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> (γₛE : ConₛA (eraseConₛ Γₛ)) -> (v : Varₛ Γₛ Aₛ) ->
  Varₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ γₛE (.var v))
| Γₛ ▹ Aₛ, .(Aₛ), ⟨γₛE, aₛE⟩, .vz => (.vz) -- because of .vz we know that Aₛ === Aₛ
| Γₛ ▹ Bₛ, Aₛ, ⟨γₛE, bₛE⟩, .vs v => by -- this is not the variable we're looking for: `Bₛ !== Aₛ`.
  -- Now `v : Varₛ Γₛ Aₛ`, so a variable in the smaller context.
  -- Example `Vec:N->U ⊢ VAR(Vec) : N -> U`.

  -- We want to cast that variable into `v' : Varₛ (guardConₛ Γₛ) (guardTyₛ Aₛ (.var v))`
  -- Example `VecG:N->VecE->U ⊢ VAR(VecG) : N -> VecE -> U`
  --
  let vG  : Varₛ (guardConₛ        Γₛ        γₛE ) (guardTyₛ (Γₛ:=Γₛ) Aₛ γₛE (.var v)) := guardVarₛ γₛE v
  -- Okay that worked, and now we adapt v' back into the larger context `Bₛ :: Γₛ`.
  let vG' : Varₛ (guardConₛ (Γₛ ▹ Bₛ) (γₛE, bₛE)) (guardTyₛ (Γₛ:=Γₛ) Aₛ γₛE (.var v)) := .vs vG

  --      ⊢ Varₛ (guardConₛ (Bₛ :: Γₛ) (bₛE, γₛE)) (guardTyₛ (Γₛ:=Bₛ::Γₛ) Aₛ (bₛE, γₛE) (.var (.vs v)))
  -- Now the problem is that
  rw [<- guardTyₛ_step]
  exact vG'

  -- -- let ih : Varₛ (guardConₛ        Γₛ        γₛE ) (guardTyₛ Bₛ γₛE (Tmₛ.var v)) := guardVarₛ γₛE v
  -- rw [guardConₛ]
  -- let ih : Varₛ (                                            guardConₛ Γₛ γₛE) (guardTyₛ Aₛ       γₛE  (Tmₛ.var          v )) := guardVarₛ γₛE v
  -- --     ⊢ Varₛ (guardTyₛ Bₛ (bₛE, γₛE) (Tmₛ.var Varₛ.vz) :: guardConₛ Γₛ γₛE) (guardTyₛ Aₛ (bₛE, γₛE) (Tmₛ.var (Varₛ.vs v)))
  -- -- fail let ih' : Varₛ (.cons (guardTyₛ Bₛ γₛE (Tmₛ.var (.vz))) (guardConₛ Γₛ γₛE)) (guardTyₛ Aₛ γₛE (Tmₛ.var v)):= Varₛ.vs ih
  -- -- let ihh := guardVarₛ _ v
  -- let ihh := (guardVarₛ (Γₛ := Bₛ :: Γₛ) ⟨bₛE, γₛE⟩ v)
  -- done

/-- Given `Γₛ ⊢ Self a₁ a₂ a₃ : U` returns `guard(Γₛ) ⊢ SelfG a₁ a₂ a₃ : SelfE -> U`.

  Challange is that we don't know which type (`Even`, `Odd`, etc) `t` refers to,
  it could be `Even @ 123` or `Odd @ 123`.
  So the output term's type needs to depend on `t`.
  -/
-- def guardTmₛ : (t : Tmₛ Γₛ U) -> Tmₛ (guardConₛ Γₛ) (SPi (TmₛA (eraseTmₛ Self) γₛE) (fun e => U))
def guardTmₛ : {Γₛ : Conₛ} -> (γₛE : ConₛA (eraseConₛ Γₛ)) -> (t : Tmₛ Γₛ Aₛ) ->
  -- Tmₛ (guardConₛ Γₛ γₛE) (SPi (TmₛA (eraseTmₛ t) γₛE) (fun e => U))
  Tmₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ γₛE t)
-- | Aₛ :: Γₛ, ⟨aₛE, γₛE⟩, .var .vz            => .var .vz
-- | Bₛ :: Γₛ, ⟨bₛE, γₛE⟩, .var (.vs v)        => by
--   -- let res := guardTmₛ (Γₛ := Bₛ :: Γₛ) ⟨bₛE, γₛE⟩ (.var v)
--   let v' := guardTmₛ γₛE (.var v)
--   let v'' : Tmₛ (guardConₛ (Bₛ :: Γₛ) (bₛE, γₛE)) (guardTyₛ Aₛ       γₛE  (.var      v )) := vshift v'
--   done
| Γₛ, γₛE, .var v              => .var (guardVarₛ γₛE v)
| Γₛ, γₛE, .app (A := _Aₛ) t u => .app (guardTmₛ γₛE t) u

#check TyₛA
/-- For example maps the `Vec.cons` ctor type
```
Vec : Nat ->          U ⊢ (n:Nat) -> (_:A) -> (_ : Vec n) -> Vec (n+1)
```
into `VecG.cons`
```
VecG : Nat -> VecE -> U ⊢ (n:Nat) -> (x:A) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons (n+1) x e)
``` -/
-- def guardTyₚ (γₛE : ConₛA (eraseₛ Γₛ)) : Tyₚ Γₛ -> Tyₚ (guardₛ Γₛ)
def guardTyₚ.{u} (γₛE : ConₛA.{u} (eraseConₛ Γₛ)) : (A : Tyₚ Γₛ) -> (aE : TyₚA (eraseTyₚ A) γₛE) -> Tyₚ (guardConₛ Γₛ γₛE)
| El         Self, aE => El (.app (guardTmₛ γₛE Self) aE) -- VecG ... (VecE.cons ...)
| PPi   T    Rest, aE => PPi T (fun t => guardTyₚ γₛE (Rest t) (aE t))
| PFunc Self Rest, aE => -- this `Self` could be from a different ind type from the mutual block!
    PPi (TmₛA (eraseTmₛ Self) γₛE) fun e =>  -- (e : SelfE) ->
      PFunc (.app (guardTmₛ γₛE Self) e) <| -- SelfG e ->
        guardTyₚ γₛE Rest (aE e)

#check guardTyₚ

def guardConₚ (γₛE : ConₛA (eraseConₛ Γₛ)) : (Γ : Conₚ Γₛ) -> (γE : ConₚA (eraseConₚ Γ) γₛE) -> Conₚ (guardConₛ Γₛ γₛE)
| ⬝, ⟨⟩ => ⬝
| Γ ▹ A, ⟨γE, aE⟩ => guardConₚ γₛE Γ γE ▹ guardTyₚ γₛE A aE

inductive VecE : Type where
| nil : VecE
| cons : Nat -> String -> VecE -> VecE

/-- VecG : Nat -> VecE -> Type -/
example : guardConₛ Vₛ ⟨⟨⟩, VecE⟩ = (⬝ ▹ SPi Nat fun _ => SPi VecE fun _ => U) := rfl

#reduce guardConₚ (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ (V String) ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩

def downₛ
  {Γₛ : Conₛ} {Γ : Conₚ Γₛ}
  (γₛ : ConₛA Γₛ) (γ : ConₚA Γ γₛ)
  (γₛE : ConₛA (eraseConₛ Γₛ)) (γE : ConₚA (eraseConₚ Γ) γₛE)
  (γₛG : ConₛA (guardConₛ Γₛ γₛE)) (γG : ConₚA (guardConₚ γₛE Γ γE) γₛG)
  : {A : Tyₚ Γₛ} -> (a : TyₚA A γₛ) -> (aE : TyₚA (eraseTyₚ A) γₛE) × TyₚA (guardTyₚ γₛE A aE) γₛG
:= sorry

#check TyₛA.{0,0} U
#check TyₚA.{0,0} (Γₛ:=Vₛ) (El (.app (.var .vz) 123)) ⟨⟨⟩, Vec String⟩
#reduce TyₚA.{0,0} (Γₛ:=Vₛ) (PPi Nat fun _n => El (.app (.var .vz) _n)) ⟨⟨⟩, Vec String⟩

def downₚ
  {Γₛ : Conₛ} {Γ : Conₚ Γₛ}
  (γₛ : ConₛA Γₛ) (γ : ConₚA Γ γₛ)
  (γₛE : ConₛA (eraseConₛ Γₛ)) (γE : ConₚA (eraseConₚ Γ) γₛE)
  (γₛG : ConₛA (guardConₛ Γₛ γₛE)) (γG : ConₚA (guardConₚ γₛE Γ γE) γₛG)
  : {A : Tyₚ Γₛ} -> (a : Tmₚ Γ A) -> (aE : Tmₚ (eraseConₚ Γ) (eraseTyₚ A)) × Tmₚ (guardConₛ Γₛ γₛE) (guardTyₚ γₛE A aE)
| El         Self, a => ⟨TmₚA (El (eraseTmₛ Self)) γₛE, El (guardTmₛ Self)⟩
| PPi   T    Rest, a => sorry
| PFunc Self Rest, a => sorry
