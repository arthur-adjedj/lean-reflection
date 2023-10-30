import Reflection.Simple.InductiveType

inductive SimpleType : Type -> Type 2
| ind  {A   : Type} : SimpleInductiveType A        -> SimpleType A
| func {A B : Type} : SimpleType A -> SimpleType B -> SimpleType (A -> B)

def Args : Type -> Type := sorry
def apply : (ctor : SCtorType T spec) -> Args T -> T := sorry

set_option genInjectivity false in
inductive SimpleValue : (T : Type) -> SimpleType T -> T -> Type 2
| ctor
  (ind : SimpleInductiveType T)
  (i : Fin ind.K)
  (args : Args T)
  : SimpleValue T (.ind ind) (apply (Get ind.ctors i).ctor args)
| lam
  {a : SimpleType A}
  {b : SimpleType B}
  (body : A -> B)
  : SimpleValue (A -> B) (.func a b) (fun (arg : A) => body arg)
| app {A B : Type}
  {a : SimpleType A}
  {b : SimpleType B}
  (f : A -> B)
  (fSimple : SimpleValue (A -> B) (SimpleType.func a b) f)
  (arg : A)
  (argSimple : SimpleValue A a arg)
  : SimpleValue B b (f arg)

set_option genInjectivity false in
/--
  If we modeled propositions as in MLTT, we would need type indices etc, and the whole point
  of having simple types is to avoid that complexity.
  Instead, we want to model propositions and predicates classically, with implications, and, or,
  less-than, etc, being primitive or just defined as functions.
-/
inductive SimpleProp : Prop -> Type 2
| tru : SimpleProp True
| fals : SimpleProp False
| not : SimpleProp α -> SimpleProp (¬α)
| and : SimpleProp α -> SimpleProp β -> SimpleProp (α ∧ β)
| or  : SimpleProp α -> SimpleProp β -> SimpleProp (α ∨ β)
| imp : SimpleProp α -> SimpleProp β -> SimpleProp (α -> β)
| foral {β : τ -> Prop} : SimpleType τ -> (∀x : τ, SimpleProp (β x)) -> SimpleProp (∀x : τ, β x)
-- | pred  {P : τ -> Prop} : SimpleValue τ hτ x -> SimpleProp (P x)


