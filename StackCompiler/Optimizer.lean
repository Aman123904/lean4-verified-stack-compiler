import StackCompiler.Compiler

/-!
# A verified constant-folding optimizer

`optimize` folds constant subterms and removes the algebraic identities
`0 + e`, `e + 0`, `1 * e`, `e * 1`, `0 * e`, `e * 0`. We prove it preserves
meaning, never grows the expression, and compose it with the compiler.
-/

namespace StackCompiler

/-- Smart constructor for addition. -/
def mkPlus : Expr → Expr → Expr
  | .const a, .const b => .const (a + b)
  | .const 0, e => e
  | e, .const 0 => e
  | a, b => .plus a b

/-- Smart constructor for multiplication. -/
def mkTimes : Expr → Expr → Expr
  | .const a, .const b => .const (a * b)
  | .const 0, _ => .const 0
  | _, .const 0 => .const 0
  | .const 1, e => e
  | e, .const 1 => e
  | a, b => .times a b

def optimize : Expr → Expr
  | .plus a b  => mkPlus (optimize a) (optimize b)
  | .times a b => mkTimes (optimize a) (optimize b)
  | e => e

theorem mkPlus_eval (env : Env) (a b : Expr) :
    (mkPlus a b).eval env = a.eval env + b.eval env := by
  unfold mkPlus; split <;> simp_all [Expr.eval]

theorem mkTimes_eval (env : Env) (a b : Expr) :
    (mkTimes a b).eval env = a.eval env * b.eval env := by
  unfold mkTimes; split <;> simp_all [Expr.eval]

/-- **Optimizer soundness.** -/
theorem optimize_eval (env : Env) (e : Expr) : (optimize e).eval env = e.eval env := by
  induction e with
  | const => rfl
  | var => rfl
  | plus a b iha ihb => simp [optimize, mkPlus_eval, iha, ihb, Expr.eval]
  | times a b iha ihb => simp [optimize, mkTimes_eval, iha, ihb, Expr.eval]

theorem mkPlus_size (a b : Expr) : (mkPlus a b).size ≤ a.size + b.size + 1 := by
  unfold mkPlus; split <;> simp [Expr.size] <;> omega

theorem mkTimes_size (a b : Expr) : (mkTimes a b).size ≤ a.size + b.size + 1 := by
  unfold mkTimes; split <;> simp [Expr.size] <;> omega

/-- The optimizer never makes an expression bigger. -/
theorem optimize_size (e : Expr) : (optimize e).size ≤ e.size := by
  induction e with
  | const => simp [optimize]
  | var => simp [optimize]
  | plus a b iha ihb =>
    have := mkPlus_size (optimize a) (optimize b)
    simp only [optimize, Expr.size]; omega
  | times a b iha ihb =>
    have := mkTimes_size (optimize a) (optimize b)
    simp only [optimize, Expr.size]; omega

/-- **End-to-end correctness** of the optimizing compiler. -/
theorem compile_optimize_correct (env : Env) (e : Expr) (s : Stack) :
    exec env (compile (optimize e)) s = e.eval env :: s := by
  rw [compile_correct, optimize_eval]

/-- The optimizing compiler never emits more code than the plain one. -/
theorem compile_optimize_shorter (e : Expr) :
    (compile (optimize e)).length ≤ (compile e).length := by
  simp only [compile_length]; exact optimize_size e

-- A worked example: `(x + 0) * (2 * 3)` optimizes to `x * 6`.
example : optimize (.times (.plus (.var "x") (.const 0)) (.times (.const 2) (.const 3)))
    = .times (.var "x") (.const 6) := by decide

end StackCompiler
