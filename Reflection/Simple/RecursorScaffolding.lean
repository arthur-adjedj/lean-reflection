import Reflection.Vec
import Reflection.Simple.Constructors
import Reflection.ListN

/- # Scaffolding types (messy thoughts)
  Maybe RecCase should return something akin to "Skipper", which will be easier to recurse through
  for users. This would then replace the CPS approach with `mots`.

  Also note that this is possible in two ways. The Iotas "Skipper" approach constructs a skipper
  trivially, and then iterates through it, returning the rec case type as the result, not the skipper anymore.

  And maybe for RecCase, constructing the "Skipper"-esque thing is the difficult part,
  and maybe we want to return the "skipper"-esque thing itself directly.

  But! Maybe this is a general code pattern, where we return a constructed inductive type which is
  easy to traverse.
  It might have a "id" thing which just returns the recursor type exactly, but maybe the user
  wants to compute something else, and then using the same "skipper"-esque inductive helper type,
  they can compute something else; for example maybe lead proofs which go through the structure
  of recursors.
  
  How do you call a helper type like that? They "go through", so in a way they are helpers for
  recursion. They also say in which way a problem becomes smaller. `RecCases` is very trivial and
  becomes smaller in obvious ways. But `RecCase` has the weird `mots` CPS thing, so it is not obvious,
  and here is where these helper types will help a lot. Walker types? Crutch type? Crane type?
  Scaffolding type? Yeah scaffolding is most fitting, it even has "folding" in its name.

  The idea is that every step through the scaffolding reduces the problem.
-/

/-
  ## Connection with Local Programming / Prolog
  The way that scaffolding types work is by creating a constraint between
  its type indices, much akin to prolog, e.g. how `plus(A, B, C)` works.
-/

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
def RecCase {mots : Prop -> Prop} (motive : T -> Prop) : @RecCaseScaffolding T motive o_ctor spec ctor args mots -> Prop
| .ground mots ctor => mots (motive ctor)
| .nonrecursive (U := U) mots sub => (x : U) -> RecCase motive (sub x)
| .recursive             mots sub =>
  -- This apparent simplicity is deceptive! The implicit `mots` parameter to the recursive invocation
  -- is actually inferred to be `fun P => mots (motive x -> P)`, due to the type of `sub` in `.recursive`.
  (x : T) -> RecCase motive (sub x)

def RecCases (motive : T -> Prop) : Vec (SCtor T) K -> Prop
| ⟦⟧ => (t : T) -> motive t
| ctor ::: rest =>
  @RecCase T ctor ctor.spec ctor.ctor ctor.args id motive (RecCaseScaffold ctor) ->
    @RecCases T _ motive rest

def Rec : Vec (SCtor T) k -> Prop
| ctors => (motive : T -> Prop) -> RecCases motive ctors


namespace Test
  #reduce @Rec Nat _ ⟦⟧
  #reduce @Rec Nat _ (⟨.nil, .zero, .head .zero⟩ ::: ⟦⟧)

  class SimpleInductiveType (T : Type) where
    K : Nat
    ctors : Vec (SCtor T) K
    recursor : Rec ctors

  instance : SimpleInductiveType Nat := {
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

  instance : SimpleInductiveType ListN := {
    ctors :=
      ⟨.nil                   , ListN.nil,  cNil⟩ :::
      ⟨.other Nat (.self .nil), ListN.cons, cCons⟩ ::: ⟦⟧
    recursor := @ListN.rec
  }

end Test
