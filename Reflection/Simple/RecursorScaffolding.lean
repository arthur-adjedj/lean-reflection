import Reflection.Vec
import Reflection.UnifyCmd
import Reflection.Simple.Constructors
import Reflection.ListN

/-- One recursor case is for example `motive ListN.nil`, or
  `(x : Nat) -> (xs : ListN) -> motive xs -> motive (x :: xs)`.
                                             ^^^^^^^^^^^^^^^^ The conclusion, which is `motive (ctorₖ a₁ a₂ ...)`.
                                ^^^^^^^^^ require motives for recursive args [motive a_{r₁}, motive a_{r₂}, ...]
   ^^^^^^^^^^^^^^^^^^^^^^^^^ args [a₁, a₂, ...]
  The `ctors` argument is all constructors.
-/
inductive RecCaseScaffolding {motive : T -> Prop} (o_ctor : SCtor T)
  : (spec : SCtorSpec) -> (ctor : SCtorType T spec) -> (args : SCtorArgs T spec ctor) -> (Prop -> Prop) -> Type 2
/-- When we get to this point, `mots` is constrained to be exactly the required hypotheses for the
  recursive args. Why? Note that we have `o_ctor`, which is the original constructor,
  but spec/ctor/args have all hit the bottom (.nil etc).
  Then when a function (e.g. `RecCase`) is given a `RecCaseScaffolding o_ctor o_ctor.spec octor.ctor octor.args id`,
  the only way to get to the ground case constrains `mots` properly once we get to the ground case.
  Although we can pick something other than `id` as the starting point.  -/
| ground
  (mots : Prop -> Prop)
  (ctor : T)
  : RecCaseScaffolding o_ctor .nil ctor (.head ctor) mots 
| recursive
  (mots : Prop -> Prop)
  (sub : (x : T) -> @RecCaseScaffolding T motive o_ctor spec' (ctor x) (args' x) (fun P => mots (motive x -> P)))
  : RecCaseScaffolding o_ctor (.self spec') (ctor) (.recursive args') (mots)
| nonrecursive
  (mots : Prop -> Prop)
  (sub : (x : U) -> @RecCaseScaffolding T motive o_ctor spec' (ctor x) (args' x) (mots))
  : RecCaseScaffolding o_ctor (.other U spec') (ctor) (.nonrecursive args') (mots)

/-- Build the scaffolding. -/
def RecCaseScaffold {motive : T -> Prop} (o_ctor : SCtor T)
  : @RecCaseScaffolding T motive o_ctor o_ctor.spec o_ctor.ctor o_ctor.args mots
  := go o_ctor.spec o_ctor.ctor o_ctor.args
where
  go {mots : Prop -> Prop} {o_ctor : SCtor T} : (spec : SCtorSpec) -> (ctor : SCtorType T spec) -> (args : SCtorArgs T spec ctor)
    -> @RecCaseScaffolding T motive o_ctor spec ctor args mots
  | .nil, ctor, args => let .head ctor := args; .ground mots ctor
  | .self spec', ctor', .recursive args' =>
      .recursive mots fun x =>
        go (mots := fun P => mots (motive x -> P)) spec' (ctor' x) (args' x)
  | .other _ spec', ctor', .nonrecursive args' => 
      .nonrecursive mots fun x =>
        go (mots := mots) spec' (ctor' x) (args' x)

/-- Uses scaffolding to construct the recursor type. -/
def RecCase (motive : T -> Prop) (o_ctor : SCtor T) (ctor : SCtor T) (mots : Prop -> Prop)
  : @RecCaseScaffolding T motive o_ctor ctor.spec ctor.ctor ctor.args mots -> Prop
  := go motive mots o_ctor
where
  /-- Literally the same as RecCase, just `ctor` unpacked. -/
  @[reducible]
  go (motive : T -> Prop) (mots : Prop -> Prop) (o_ctor : SCtor T) {spec} {ctor} {args}
  : @RecCaseScaffolding T motive o_ctor spec ctor args mots -> Prop
  | .ground mots ctor => mots (motive ctor)
  | .nonrecursive (U := U) mots sub => (x : U) -> go motive mots o_ctor (sub x)
  | .recursive             mots sub =>
    -- This apparent simplicity is deceptive! The implicit `mots` parameter to the recursive invocation
    -- is actually inferred to be `fun P => mots (motive x -> P)`, due to the type of `sub` in `.recursive`.
    (x : T) -> go motive _ o_ctor (sub x)
    -- This would have also worked, but I think it's cool that Lean is able to infer it all on its own:
    -- (x : T) -> go motive (fun P => mots (motive x -> P)) o_ctor (sub x)

def RecCases (motive : T -> Prop) : Vec (SCtor T) K -> Prop
| ⟦⟧ => (t : T) -> motive t
| ctor ::: ctors' =>
  RecCase motive ctor ctor id (RecCaseScaffold ctor) ->
    RecCases motive ctors'

def Rec : Vec (SCtor T) k -> Prop
| ctors => (motive : T -> Prop) -> RecCases motive ctors


namespace Test
  #reduce @Rec Nat _ ⟦⟧
  #reduce @Rec Nat _ (⟨.nil, .zero, .head .zero⟩ ::: ⟦⟧)

  class _SimpleInductiveTypeRecOnly (T : Type) where
    K : Nat
    ctors : Vec (SCtor T) K
    recursor : Rec ctors

  instance : _SimpleInductiveTypeRecOnly Nat := {
    ctors :=
      ⟨.nil      , Nat.zero, SCtorArgs.head Nat.zero⟩ :::
      ⟨.self .nil, Nat.succ, SCtorArgs.recursive fun (n : Nat) => SCtorArgs.head (Nat.succ n)⟩ ::: ⟦⟧
    recursor := @Nat.rec
  }

  def cNil : SCtorArgs ListN (.nil) ListN.nil :=
    SCtorArgs.head ListN.nil
  def cCons : SCtorArgs ListN (.other Nat (.self .nil)) ListN.cons :=
    SCtorArgs.nonrecursive fun (n : Nat) =>
      SCtorArgs.recursive fun (list : ListN) =>
        SCtorArgs.head <| ListN.cons n list

  instance listn : _SimpleInductiveTypeRecOnly ListN := {
    ctors :=
      ⟨.nil                   , ListN.nil,  cNil⟩ :::
      ⟨.other Nat (.self .nil), ListN.cons, cCons⟩ ::: ⟦⟧
    recursor := @ListN.rec
  }

  #unify Rec listn.ctors =?= ({motive : ListN → Prop} →
    motive .nil →
    ((a : Nat) → (a_1 : ListN) → ?b → motive (ListN.cons a a_1)) →
    ?asdf
    -- (t : ListN) →
    -- motive t
  )

end Test
