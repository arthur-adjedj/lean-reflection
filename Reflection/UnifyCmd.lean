import Lean

open Lean Elab Command Meta Term
elab "#unify" lhs:term " =?= " rhs:term : command => do
  liftTermElabM do
    let lhs <- elabTerm lhs none
    let rhs <- elabTerm rhs none
    let holes := rhs.collectMVars default |>.result
    holes.forM fun h => h.setKind .natural
    if <- isDefEq lhs rhs then
      let assignments <- holes.mapM fun h => do
        let name := (<- h.getDecl).userName
        let val <- instantiateMVars (Expr.mvar h)
        pure m!"{name} ↦ {val}"
      logInfo m!"{assignments}"
    else
      logError "Nu-uh!"

#unify List Nat =?= List ?a
#unify (α : Type) -> List α =?= (α : Type) -> List ?hole