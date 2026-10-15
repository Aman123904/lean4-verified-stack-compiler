import StackCompiler.Expr

/-!
# Target machine

A stack machine with four instructions. Running a program is
compositional: executing `p ++ q` is executing `p` and then `q`.
-/

namespace StackCompiler

inductive Instr where
  | push : Nat → Instr
  | load : String → Instr
  | add  : Instr
  | mul  : Instr
  deriving Repr, DecidableEq

abbrev Stack := List Nat

/-- Execute a program. On stack underflow an arithmetic instruction is a no-op. -/
def exec (env : Env) : List Instr → Stack → Stack
  | [], s => s
  | .push n :: is, s => exec env is (n :: s)
  | .load x :: is, s => exec env is (env x :: s)
  | .add :: is, b :: a :: s => exec env is ((a + b) :: s)
  | .mul :: is, b :: a :: s => exec env is ((a * b) :: s)
  | _ :: is, s => exec env is s

/-- Execution distributes over program concatenation. -/
theorem exec_append (env : Env) (p q : List Instr) (s : Stack) :
    exec env (p ++ q) s = exec env q (exec env p s) := by
  induction p generalizing s with
  | nil => rfl
  | cons i p ih =>
    match i, s with
    | .push _, _ => simp [exec, ih]
    | .load _, _ => simp [exec, ih]
    | .add, b :: a :: s => simp [exec, ih]
    | .add, [] => simp [exec, ih]
    | .add, [_] => simp [exec, ih]
    | .mul, b :: a :: s => simp [exec, ih]
    | .mul, [] => simp [exec, ih]
    | .mul, [_] => simp [exec, ih]

end StackCompiler
