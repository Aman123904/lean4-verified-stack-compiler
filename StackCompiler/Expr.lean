/-!
# Source language

A tiny arithmetic expression language with constants, variables,
addition and multiplication, together with its denotational semantics.
-/

namespace StackCompiler

/-- Variable environments map names to natural numbers. -/
abbrev Env := String → Nat

/-- Arithmetic expressions. -/
inductive Expr where
  | const : Nat → Expr
  | var   : String → Expr
  | plus  : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr, DecidableEq

/-- Reference semantics: evaluate an expression in an environment. -/
def Expr.eval (env : Env) : Expr → Nat
  | .const n   => n
  | .var x     => env x
  | .plus a b  => a.eval env + b.eval env
  | .times a b => a.eval env * b.eval env

/-- Number of nodes in an expression. -/
def Expr.size : Expr → Nat
  | .const _   => 1
  | .var _     => 1
  | .plus a b  => a.size + b.size + 1
  | .times a b => a.size + b.size + 1

end StackCompiler
