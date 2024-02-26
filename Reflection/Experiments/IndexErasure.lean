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

def eraseVarₚ : Varₚ Γ A -> Varₚ (eraseConₚ Γ) (eraseTyₚ A)
| .vz => .vz
| .vs v => .vs (eraseVarₚ v)

def eraseTmₚ : Tmₚ Γ A -> Tmₚ (eraseConₚ Γ) (eraseTyₚ A)
| .var v => .var (eraseVarₚ v)
| .app (A := _A) t u => .app (eraseTmₚ t) u
| .appr t u => .appr (eraseTmₚ t) (eraseTmₚ u)

-- # Guard


/-- For example maps `Vec : Nat -> U` to `VecG : Nat -> VecE -> U`. -/
def guardTyₛ' : (Aₛ : Tyₛ.{u}) -> TyₛA.{u, u} (eraseTyₛ Aₛ) -> Tyₛ.{u}
| U         , aₛE => SPi aₛE (fun _ => U)
| SPi T Rest, aₛE => SPi T   (fun t => guardTyₛ' (Rest t) aₛE)


/-- Given a `Γₛ ⊢ Self a₁ a₂ a₃ : U` (note the type `U`),
  computes the type `SelfE -> U` for `(guard Γₛ) ⊢ SelfG a₁ a₂ a₃ : SelfE -> U`. -/
def guardTyₛ : (Aₛ : Tyₛ) -> (γₛE : ConₛA.{u, u} (eraseConₛ Γₛ)) -> (t : Tmₛ Γₛ Aₛ) -> Tyₛ
| U      , γₛE, tm => SPi (TmₛA (eraseTmₛ tm) γₛE) fun _ => U
| SPi T f, γₛE, tm => SPi T                        fun τ => guardTyₛ (f τ) γₛE (.app tm τ)

-- example : guardTyₛ' Aₛ aₛE = guardTyₛ (Γₛ := Γₛ ▹ Aₛ) Aₛ ⟨γₛE, aₛE⟩ (.var .vz) := by
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
| Γₛ ▹ Aₛ, ⟨γₛE, aₛE⟩ => guardConₛ Γₛ γₛE ▹ guardTyₛ (Γₛ := Γₛ ▹ Aₛ) Aₛ ⟨γₛE, aₛE⟩ (.var .vz)


set_option trace.aesop true

theorem guardTyₛ_step (v : Varₛ Γₛ Aₛ) : guardTyₛ Aₛ γₛE (.var v) = @guardTyₛ (Γₛ ▹ Bₛ) Aₛ (γₛE, bₛE) (.var (.vs v)) := by
  induction Aₛ with
  | U =>
    -- most scuffed proof
    simp only [guardTyₛ]
    simp only [eraseTmₛ]
    simp [VarₛA]
    rw [TmₛA_var]
    rw [TmₛA_var]
    rfl
  | SPi T A ih =>
    rw [guardTyₛ]
    rw [guardTyₛ]
    simp [guardTyₛ]
    apply funext
    intro u
    have := ih u
    exact ih u (v)
    sorry
    done

def guardVarₛ_asdfasdfkljh :
  {Γₛ : Conₛ} ->
  (γₛE : ConₛA (eraseConₛ Γₛ)) ->
  (bₛE : TyₛA U) ->
  (v : Varₛ Γₛ Aₛ) ->
  Varₛ (guardConₛ  Γₛ         γₛE      ) (guardTyₛ (Γₛ:=Γₛ    ) Aₛ  γₛE       (.var      v )) ->
  Varₛ (guardConₛ (Γₛ ▹ Bₛ) (γₛE, bₛE)) (guardTyₛ (Γₛ:=Γₛ▹Bₛ) Aₛ (γₛE, bₛE) (.var (.vs v)))
| Γₛ ▹ Cₛ, ⟨γₛE, cₛE⟩, bₛE, .vz, oo => by
  -- let ⟨γₛE, cₛE⟩ := γₛE
  sorry
| _, γₛE, bₛE, .vs v, o => sorry

/-- Given a variable `Vec:N->U ⊢ VAR(Vec) : N->U`, we return `VecG:N->VecE->U ⊢ VAR(VecG) : N->VecE->U`.
  The runtime de-brujin value of this variable doesn't change. So this is basically just a cast operator. -/
def guardVarₛ : {Γₛ : Conₛ} -> {Aₛ : Tyₛ} -> (γₛE : ConₛA (eraseConₛ Γₛ)) ->
  (v : Varₛ Γₛ Aₛ) ->
  Varₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ γₛE (.var v))
| Γₛ ▹ Aₛ, .(Aₛ), ⟨γₛE, aₛE⟩, .vz => .vz -- because of .vz we know that Aₛ === Aₛ
| Γₛ ▹ Bₛ, Aₛ, ⟨γₛE, bₛE⟩, .vs v => by -- this is not the variable we're looking for: `Bₛ !== Aₛ`.
  have : guardConₛ (Γₛ ▹ Bₛ) (γₛE, bₛE) = Conₛ.ext (guardConₛ Γₛ γₛE) (guardTyₛ Bₛ γₛE (.var <| sorry)) := sorry
  rw [this]
  let ih := guardVarₛ γₛE v
  exact .vs ih
  -- Now `v : Varₛ Γₛ Aₛ`, so a variable in the smaller context.
  -- Example `Vec:N->U ⊢ VAR(Vec) : N -> U`.

  -- We want to cast that variable into `v' : Varₛ (guardConₛ Γₛ) (guardTyₛ Aₛ (.var v))`
  -- Example `VecG:N->VecE->U ⊢ VAR(VecG) : N -> VecE -> U`
  let vG  : Varₛ (guardConₛ  Γₛ         γₛE      ) (guardTyₛ (Γₛ:=Γₛ) Aₛ γₛE (.var v)) := guardVarₛ γₛE v
  let vG' : Varₛ (guardConₛ (Γₛ ▹ Bₛ) (γₛE, bₛE)) (guardTyₛ (Γₛ:=Γₛ) Aₛ γₛE (.var v)) := .vs vG
  --      ⊢ Varₛ (guardConₛ (Γₛ ▹ Bₛ) (γₛE, bₛE)) (guardTyₛ (Γₛ:=Γₛ▹Bₛ) Aₛ (γₛE, bₛE) (.var (.vs v)))
  -- TODO Try similar approach to SubₛA_weaken
  rw [<- guardTyₛ_step] -- this uses `sorry`
  exact vG'



-- #exit

/-- Given `Γₛ ⊢ Self a₁ a₂ a₃ : U` returns `guard(Γₛ) ⊢ SelfG a₁ a₂ a₃ : SelfE -> U`.

  Challange is that we don't know which type (`Even`, `Odd`, etc) `t` refers to,
  it could be `Even @ 123` or `Odd @ 123`.
  So the output term's type needs to depend on `t`.
  -/
def guardTmₛ : {Γₛ : Conₛ} -> (γₛE : ConₛA (eraseConₛ Γₛ)) -> (t : Tmₛ Γₛ Aₛ) -> Tmₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ γₛE t)
| Γₛ, γₛE, .var v              => .var (guardVarₛ γₛE v)
| Γₛ, γₛE, .app (A := _Aₛ) t u => .app (guardTmₛ γₛE t) u

/-- For example maps the `Vec.cons` ctor of type
```
Vec : Nat ->          U ⊢ (n:Nat) -> (_:A) -> (_ : Vec n) ->            Vec (n+1)
```
into `VecG.cons` of type
```
VecG : Nat -> VecE -> U ⊢ (n:Nat) -> (x:A) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons (n+1) x e)
``` -/
def guardTyₚ.{u} (γₛE : ConₛA.{u} (eraseConₛ Γₛ)) : (A : Tyₚ Γₛ) -> (aE : TyₚA (eraseTyₚ A) γₛE) -> Tyₚ (guardConₛ Γₛ γₛE)
| El         Self, aE => El (.app (guardTmₛ γₛE Self) aE) -- VecG ... (VecE.cons ...)
| PPi   T    Rest, aE => PPi T (fun t => guardTyₚ γₛE (Rest t) (aE t))
| PFunc Self Rest, aE => -- this `Self` could be from a different ind type from the mutual block!
    PPi (TmₛA (eraseTmₛ Self) γₛE) fun e =>  -- (e : SelfE) ->
      PFunc (.app (guardTmₛ γₛE Self) e) <| -- SelfG e ->
        guardTyₚ γₛE Rest (aE e)

def guardConₚ (γₛE : ConₛA (eraseConₛ Γₛ)) : (Γ : Conₚ Γₛ) -> (γE : ConₚA (eraseConₚ Γ) γₛE) -> Conₚ (guardConₛ Γₛ γₛE)
| ⬝, ⟨⟩ => ⬝
| Γ ▹ A, ⟨γE, aE⟩ => guardConₚ γₛE Γ γE ▹ guardTyₚ γₛE A aE


/-- ! Cast `"Vec.cons"` to `"VecG.cons"`. -/
def guardVarₚ : {Γ : Conₚ Γₛ} -> {A : Tyₚ Γₛ} -> (γₛE : ConₛA (eraseConₛ Γₛ)) -> (γE : ConₚA (eraseConₚ Γ) γₛE) ->
  (v : Varₚ Γ A) ->
  Varₚ (guardConₚ γₛE Γ γE) (guardTyₚ γₛE A (TmₚA (.var <| eraseVarₚ v) γE))
| Γ ▹ A, .(A), γₛE, γE, .vz => .vz
| Γ ▹ B,   A , γₛE, ⟨γE, bE⟩, .vs v => .vs (guardVarₚ γₛE γE v)


#exit

/-- Given `"Vec.cons n x v" : "Vec n"`, we change it to `"VecG.cons n x v vG" : "VecG n (VecE.cons n x v)"`.
  Here, note that we construct `"vG" : "VecG n v"`; in general for every inductive argument. -/
def guardTmₚ (γₛE : ConₛA (eraseConₛ Γₛ)) (γE : ConₚA (eraseConₚ Γ) γₛE)
  : (tm : Tmₚ Γ A) ->
    Tmₚ (guardConₚ γₛE Γ γE) (guardTyₚ γₛE A (TmₚA (eraseTmₚ tm) γE))
| Tmₚ.var v => .var (guardVarₚ γₛE γE v)
| Tmₚ.app (A := _A) t u => .app (guardTmₚ γₛE γE t) u
| Tmₚ.appr t u =>
  let e := TmₚA (eraseTmₚ u) γE
  let g := guardTmₚ γₛE γE u
  .appr (.app (guardTmₚ γₛE γE t) e) g

#print axioms guardTmₚ
#print axioms guardVarₚ
#print axioms eraseTmₚ

inductive VecE : Type where
| nil : VecE
| cons : Nat -> String -> VecE -> VecE

#reduce guardTmₚ (Γₛ := Vₛ) (Γ := V String) ⟨⟨⟩, VecE⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ (.var .vz)
#reduce guardTmₚ (Γₛ := Vₛ) (Γ := V String) ⟨⟨⟩, VecE⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ (.var (.vs .vz))

/-- VecG : Nat -> VecE -> Type -/
example : guardConₛ Vₛ ⟨⟨⟩, VecE⟩ = (⬝ ▹ SPi Nat fun _ => SPi VecE fun _ => U) := rfl

#reduce guardConₚ (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ (V String) ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩


-- def TmₛE (Γₛ : Conₛ) (Aₛ : Tyₛ) : Type 1 := Tmₛ (eraseConₛ Γₛ) (eraseTyₛ Aₛ)
-- def TmₛG (Γₛ : Conₛ) (Aₛ : Tyₛ) {γₛE : ConₛA (eraseConₛ Γₛ)} : Type 1 := Tmₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ γₛE a)
def TmₛL {Γₛ : Conₛ} {Aₛ : Tyₛ} (γₛE : ConₛA (eraseConₛ Γₛ)) (a : Tmₛ Γₛ Aₛ) : Type 1
  := Tmₛ (eraseConₛ Γₛ) (eraseTyₛ Aₛ) × Tmₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ γₛE a)

/-- For example maps `"Vec 123"` to `⟨("VecE", "VecG 123 e"⟩`. -/
def lowerₛ (γₛE : ConₛA (eraseConₛ Γₛ)) (a : Tmₛ Γₛ Aₛ) : TmₛL γₛE a
  := ⟨eraseTmₛ a, guardTmₛ γₛE a⟩
#check Sigma

/-- We want to obtain the actual `(e : VecE) × VecG e`. -/
def lowerₛA {Aₛ : Tyₛ} {γₛE : ConₛA.{0, 0} (eraseConₛ Γₛ)} {γₛG : ConₛA (guardConₛ Γₛ γₛE)} (a : Tmₛ Γₛ U) : Type 1
  := @Sigma (TmₛA (eraseTmₛ a) γₛE) (TmₛA (guardTmₛ γₛE a) γₛG)

/-- `"Vec 123" : "U"` becomes `⟨"VecE", "VecG 123"⟩ : "U" × "VecE -> U"` -/
example : lowerₛ (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ (.app (.var .vz) 123)
  = ⟨Tmₛ.var Varₛ.vz, Tmₛ.app (Tmₛ.var Varₛ.vz) 123⟩ := rfl

def lowerₚ (γₛE : ConₛA (eraseConₛ Γₛ)) (γE : ConₚA (eraseConₚ Γ) γₛE) (a : Tmₚ Γ A)
  : (aE : Tmₚ (eraseConₚ Γ) (eraseTyₚ A)) × Tmₚ (guardConₚ γₛE Γ γE) (guardTyₚ γₛE A (TmₚA aE γE))
  := ⟨eraseTmₚ a, guardTmₚ γₛE γE a⟩

def upₛ : TmₛL γₛE a -> Tmₛ Γₛ Aₛ
  := sorry

theorem lower_up : upₛ (lowerₛ γₛE a) = a := sorry

theorem reconstruct : TmₛA (lowerₛ γₛE s) γₛE -> TmₛA s γₛ
  := sorry
