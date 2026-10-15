# Verified Stack Compiler in Lean 4

[![Lean CI](https://github.com/Aman123904/lean4-verified-stack-compiler/actions/workflows/ci.yml/badge.svg)](https://github.com/Aman123904/lean4-verified-stack-compiler/actions/workflows/ci.yml)

A small but complete **verified compiler**. Arithmetic expressions compile to code for a stack machine, and the compiler is proved correct in Lean 4. It also has a constant-folding optimizer, proved to preserve meaning. It uses no Mathlib and has no `sorry`.

## Main theorems

| Theorem | Statement |
|---|---|
| `exec_append` | Running `p ++ q` runs `p` and then `q`. |
| `compile_correct` | `exec env (compile e) s = e.eval env :: s` |
| `compile_length` | The compiled code has one instruction per AST node. |
| `optimize_eval` | Constant folding preserves semantics. |
| `optimize_size` | The optimizer never grows an expression. |
| `compile_optimize_correct` | End-to-end correctness of the optimizing compiler. |

## Layout

- `StackCompiler/Expr.lean`: source language and its semantics
- `StackCompiler/Machine.lean`: stack machine and compositional execution
- `StackCompiler/Compiler.lean`: compiler and correctness proof
- `StackCompiler/Optimizer.lean`: verified constant folding

## Build

```bash
lake build
```

Toolchain: `leanprover/lean4:v4.34.1` (installed automatically by [elan](https://github.com/leanprover/elan)).
