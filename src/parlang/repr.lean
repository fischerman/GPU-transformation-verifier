import parlang.defs

namespace parlang
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

open expr
open kernel

meta def expr.repr : expr → string
| (var n)                := "(var " ++ repr n ++ ")"
| (sort l)               := "sort"
| (const n ls)           := "(const " ++ n.to_string ++ ")"
| (mvar n m t)           := "(mvar " ++ n.to_string ++ " " ++ m.to_string ++ " " ++ expr.repr t ++ ")"
| (local_const n m bi t) := "(local_const " ++ n.to_string ++ " " ++ m.to_string ++ " " ++ expr.repr t ++ ")"
| (app e f)              := "(app " ++ expr.repr e ++ " " ++ expr.repr f ++ ")"
| (lam n bi e t)         := "(lam " ++ n.to_string ++ " " ++ expr.repr e ++ " " ++ expr.repr t ++ ")"
| (pi n bi e t)          := "(pi " ++ n.to_string ++ " " ++ expr.repr e ++ " " ++ expr.repr t ++ ")"
| (elet n g e f)         := "(elet " ++ n.to_string ++ " " ++ expr.repr g ++ " " ++ expr.repr e ++ " " ++ expr.repr f ++ ")"
| (macro d args)         := "macro"

meta def name_to_expr (h : name) : tactic unit := do
  e ← tactic.get_local h,
  tactic.exact `(expr.repr e)

meta def kernel.repr : kernel σ τ → string
| (load l) := "load " ++ ""
| (store _) := "store " ++ ""
| (compute f) := "compute " ++ "" -- (by name_to_expr `f)
| (a ;; b) := kernel.repr a ++ " ;;\n" ++ kernel.repr b
| (sync) := "sync"
| (ite _ th el) := "if () {\n" ++ kernel.repr th ++ "\n} else {\n" ++ kernel.repr el ++ "\n}"
| (loop c body) := "loop (...) {\n" ++ kernel.repr body ++ "\n}"

-- instance kernel_repr_class : has_repr (kernel σ τ) := ⟨kernel.repr⟩

meta def program.repr : program σ τ → string
| (program.intro f k) := "foreach (...) {\n" ++ ((to_fmt (kernel.repr k)).nest 4).to_string ++ "\n}"

meta instance program_repr_class : has_repr (program σ τ) := ⟨program.repr⟩

end parlang