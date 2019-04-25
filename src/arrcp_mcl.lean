import mcl
import parlang
open mcl
open mcl.mclk

namespace arrcp_mcl

def sig : signature
| _ := { scope := scope.global, type := type.int }

def arrcp₁ : mclp sig := mclp.intro (λ m, 10) (mclk.global_assign "b" (expression.const_int 7 (by refl)))

def arrcp₂ : mclp sig := mclp.intro (λ m, 10) (mclk.global_assign "c" (expression.const_int 9 (by refl)))


example (c) : mclp_to_program arrcp₁ = c := begin
    rw arrcp₁,
    rw [mclp_to_program, mclk_to_kernel, prepend_load_expr, load_global_vars_for_expr],
    unfold append,
    rw list.append,
    rw parlang.list_to_kernel_seq,
    repeat {rw list.foldl},
end

#eval mclp_to_program arrcp₁
#check ```(mclp_to_program arrcp₁)
#print mclp_to_program

def X : ℕ → ℕ := λ n, n + 2

meta def num_args : expr → nat
| (expr.app f a) := num_args f + 1
| e:=0

#check X
#check `(X)
#eval parlang.expr.repr `(X)

example : mclp_rel (λ m₁ m₂, sorry) arrcp₁ arrcp₂ (λ m₁ m₂, sorry) := begin
    
end

end arrcp_mcl