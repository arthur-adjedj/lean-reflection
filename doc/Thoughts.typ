#import "@preview/cetz:0.2.2"
#import "LeanCode.typ": *

#set page(margin: 5em)
#set heading(numbering: "1.1")
#set text(font: "New Computer Modern Sans")
#show heading: set block(below: 0.9em)
#show heading: set block(above: 1.5em)
// #set math.equation(background: "red")
// #show math.equation: 

#align(center)[#text(size:1.5em)[Lean Typecodes]]
// Leanception: Metaprogramming in the object language.


// #text(center)[asdf]

// #align(center)[#box(outset: 3em)[
//   #text(weight: "bold")[Abstract]\
//   #align(left)[
//     Content goes here\
//     asdf
//   ]
// ]]


= Introduction
Lean Metaprogramming is awesome, but it works on _preterms_ `Expr`, which may be ill-typed.

In order to be able to reason about something, it needs to be a mathematical object inside our language.
For example, the $n$ in $n : NN ⊢ n + 3$ is a mathematical object; it will show up in the Lean infoview,
we can play around with $n$ such as pattern match on it.
Most importantly, $n$ is well-typed, we know that it is a natural number, and thus we know that we
can apply the eliminator for natural numbers to it.
In this sense, mathematical objects such as $n$ are _tangible_.
The compiler will complain at compile-time if we make a mistake.
// Lean metaprogramming is not tangible.

Lean metaprogramming on the other hand works with untyped `Expr`.
As such it is easy to slip up when writing metaprograms.
We have no guarantee that our metaprograms work on all possible inputs.
This is particularly bothersome for a dependently-typed langauge such as Lean, where it is easy
to forget a dependency, or make an assumption which is not true about the input `Expr`.
For metaprograms, "runtime" is the compile-time of normal programs.
We have the same issue from languages like C\#, Java, etc, where we rely on extensive testing;
we can only do point-wise tests for conrete inputs and check whether things explode for that concrete input.

But what if we could prove our metaprograms both correct and total?
We have little hope proving anything about Lean's existing metaprogramming capabilities, as
metaprogramming functions are often `partial`, and many optimizations such as `Expr.proj` exist
which result in a fairly complicated metaprogramming language.

// == Type-safe "meta"-programming

== Codes
We can define _codes_, and then interpret these codes.

There is a bunch of literature on this subject already. Most notably:
- Syntax for mutual inductive types by Jakob von Raumer.
- tt-in-tt

== Codes for Mutual Inductive Types (MITs)

== Codes for Dependently-Typed Terms
(Existing literature overview.)

The tt-in-tt paper uses a quotient inductive-inductive type (QIIT),
which is a weaker form of higher-inductive types (HITs).

= Type Index Erasure using Codes for MITs
A _type index_ in Lean is for example the `3` in `Vec String 3`.
Most SMT solvers do not support type indices, and so we need to express the constraint that the
type indices impose in a different way.
We split up $"Vec" : "Type" -> NN -> "Type"$ up into its type-index-erased part $"VecE" : "Type"$
and a guarding predicate $"VecG" : "Type" -> (n : NN) -> "VecE" -> "Prop"$ which asserts the length
of the erased vector.

// It is possible to derive the erased and guarding inductive types via Lean metaprogramming,
// but we can do something much cooler.

== Erase

== Guard

== Lower = $Sigma "Erase" "Guard"$

= Codes for Terms

Codes for MITs are easy because dependent function types only occur in `Ty.SPi`, which is a
dependency on an external type, and as such we can use an actual function there.
Inductive occurences of the inductive type being declared can not be dependent.

But for terms, we can have actual dependent functions, which makes things harder.
Most notably, we need substitution while specifying some constructors, as the following naive
approach does not typecheck.
`Tm Γ B` is ill-typed, because $Γ, x:A ⊢ B type$, but we expect something "$Γ ⊢ B type$".
```lean
inductive Tm : (Γ : Con) → (A : Ty Γ) → Type where
| app : (Γ : Con) -> (A : Ty Γ) -> (B : Ty (Con.ext Γ A)) ->
        (f : Tm Γ (Ty.pi Γ A B)) ->
        (a : Tm Γ A) ->
        Tm Γ B
```

The solution to this problem is an _inductive-inductive-recursive type_ (IIRT),
where we define `Con`, `Ty`, `Tm` as inductive types, and substitution as a recursive function
on those types, all in the same mutual block.

So far, codes for dependent terms have been studied as quotient inductive-inductive types (QIIT),
see for example Ambrus Kaposi's work.
The QIIT approach requires many additional constructors which emulate invoking substitutions,
and then defining the quotient of those types by specifying the expected substitution computation
rules as equalities to the quotient, and along with some additional rules such as associativity
of substitution.

I am not aware of any approach with IIRTs.
IIRTs are promising because you hopefully get better computational properties, and a more natural
representation.
Lean does not support either inductive-inductive (IIT) or inductive-recursive (IRT) types, and
definitely not both together, but pretending that it does, the resulting ideal IIRT can be found
in @originaliirt.
This does not yet include a way of adding new mutual inductive types, but that can be easily
retrofitted later by adding a new constructor `Ty.mutualinductive ...`.

#figure(caption: [The original IIRT for dependently typed terms, not feasible (directly) in Lean 4.])[
```lean
mutual
  inductive Con : Type
  | nil : Con
  | ext : (Γ : Con) -> (A : Ty Γ) -> Con

  inductive Ty : Con -> Type
  | U : Ty Γ
  | El : Tm Γ U -> Ty Γ
  | Pi : (A : Ty Γ) -> (B : Ty (ext Γ A)) -> Ty Γ

  inductive Tm : (Γ : Con) -> Ty Γ -> Type
  | var : Var Γ A -> Tm Γ A
  | app : {A : Ty Γ} ->
          {B : Ty (ext Γ A)} ->
          (f : Tm Γ (Pi A B)) ->
          (a : Tm Γ A) ->
          Tm Γ B[Var.vz ↦ a]
  | lam : {A : Ty Γ} ->
          {B : Ty (ext Γ A)} ->
          (body : Tm (ext Γ A) B) ->
          Tm Γ (Pi A B)

  inductive Subst : (Γ : Con) -> (Δ : Con) -> Type
  | nil : Subst Γ .nil
  | cons : (δ : Subst Γ Δ) -> Tm Γ (substTy δ A) -> Subst Γ (Δ, A)

  def substTy {Γ Δ : Con} : Ty Δ -> Subst Γ Δ -> Ty Γ
  | U, σ => U
  | El Self, σ => El (substTm Self σ)
  | Pi A B, σ => ???
  | mind, σ => ???

  def substTm {Γ Δ : Con} : Tm Δ A -> (σ : Subst Γ Δ) -> Tm Γ A[σ]
  | var v, σ => substVar v σ
  | app f a, σ => app (substTm f σ) ?a
  | lam body, σ => ???
end
```] <originaliirt>