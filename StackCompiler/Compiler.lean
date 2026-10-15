import StackCompiler.Machine

/-!
# The compiler and its correctness theorem
-/

namespace StackCompiler

/-- Compile an expression to postfix stack code. -/
def compile : Expr → List Instr
  | .const n   => [.push n]
  | .var x     => [.load x]
  | .plus a b  => compile a ++ compile b ++ [.add]
  | .times a b => compile a ++ compile b ++ [.mul]

/-- **Compiler correctness.** Running compiled code pushes exactly the value
of the source expression, leaving the rest of the stack untouched. -/
theorem compile_correct (env : Env) (e : Expr) (s : Stack) :
    exec env (compile e) s = e.eval env :: s := by
  induction e generalizing s with
  | const n => rfl
  | var x => rfl
  | plus a b iha ihb => simp [compile, exec_append, iha, ihb, exec, Expr.eval]
  | times a b iha ihb => simp [compile, exec_append, iha, ihb, exec, Expr.eval]

/-- Corollary: on an empty stack, the machine computes the expression's value. -/
theorem compile_correct_empty (env : Env) (e : Expr) :
    exec env (compile e) [] = [e.eval env] :=
  compile_correct env e []

/-- The generated code has exactly one instruction per expression node. -/
theorem compile_length (e : Expr) : (compile e).length = e.size := by
  induction e with
  | const => rfl
  | var => rfl
  | plus a b iha ihb => simp [compile, Expr.size, iha, ihb]; omega
  | times a b iha ihb => simp [compile, Expr.size, iha, ihb]; omega

end StackCompiler
