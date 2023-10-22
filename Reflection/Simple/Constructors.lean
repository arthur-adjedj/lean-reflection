/-
  # Ctor Spec
-/

inductive SCtorSpec : Type 1 where
| nil   :                      SCtorSpec
| self  :         SCtorSpec -> SCtorSpec
| other : Type -> SCtorSpec -> SCtorSpec

def SCtorType (T : Type) : SCtorSpec -> Type
| .nil          => T
| .self    tail => T -> SCtorType T tail
| .other U tail => U -> SCtorType T tail

inductive SCtorArgs : (T : Type) -> (spec : SCtorSpec) -> SCtorType T spec -> Type 1
| head         : (f : T)                                 -> SCtorArgs T  .nil               f
| recursive    : ((x : T) -> SCtorArgs T specTail (f x)) -> SCtorArgs T (.self    specTail) f
| nonrecursive : ((x : U) -> SCtorArgs T specTail (f x)) -> SCtorArgs T (.other U specTail) f

structure SCtor (T : Type) where
  spec : SCtorSpec
  ctor : SCtorType T spec
  args : SCtorArgs T spec ctor

def SCtorSpec.len : SCtorSpec -> Nat
| .nil => 0
| .self tail => 1 + tail.len
| .other _ tail => 1 + tail.len

def SCtorSpec.Get (T : Type) : (spec : SCtorSpec) -> (i : Fin spec.len) -> Type
| .nil         , dumb => Fin.elim0 dumb
| .self       _, ⟨0, _⟩ => T
| .self    tail, ⟨.succ n, hn⟩ => tail.Get T ⟨n, sorry⟩
| .other U    _, ⟨0, _⟩ => U
| .other _ tail, ⟨.succ n, hn⟩ => tail.Get T ⟨n, sorry⟩
