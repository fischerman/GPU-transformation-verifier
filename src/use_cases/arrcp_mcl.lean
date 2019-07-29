/- import mcl
import parlang
open mcl
open mcl.mclk


namespace arrcp_mcl

-- open classical
-- local attribute [instance] prop_decidable
-- instance a : decidable_eq string := sorry

#check ([5] : vector _ _)


def sig : signature --:= λ n, if n = "i" then { scope := scope.tlocal, type := ⟨_, [1], type.int⟩ } else { scope := scope.global, type := ⟨_, [100], type.int⟩ }
| "i" := { scope := scope.tlocal, type := ⟨_, [1], type.int⟩ }
| "tid" := { scope := scope.tlocal, type := ⟨_, [1], type.int⟩ }
| _ := { scope := scope.global, type := ⟨_, [100], type.int⟩ }

lemma i_is_tlocal : is_tlocal (sig "i") := by apply eq.refl
lemma a_is_global : is_global (sig "a") := by apply eq.refl
lemma tid_is_tlocal : is_tlocal (sig "tid") := by apply eq.refl

def read_i := (expression.tlocal_var "i" (λ_, 0) (show type_of (sig "i") = type.int, by apply eq.refl) (by refl) i_is_tlocal)
def read_tid := (expression.tlocal_var "tid" (λ_, 0) (show type_of (sig "tid") = type.int, by apply eq.refl) (show (sig "tid").type.dim = 1, by apply eq.refl) tid_is_tlocal)

def arrcp₁ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "b" [read_tid] (by refl) (expression.global_var "a" (λ_, read_tid) (show type_of (sig "a") = type.int, by refl) (by refl) a_is_global)
)


def arrcp₂ : mclp sig := mclp.intro (λ m, 10) (mclk.for "i" (by refl) (by refl) read_tid (read_i < 100) (mclk.tlocal_assign "i" [1] (show ((sig "i").type).dim = vector.length [1], by refl) (read_i + read_tid)) (
    mclk.global_assign "b" [read_i] (by refl) (expression.global_var "a" (λ_, read_i) (show type_of (sig "a") = type.int, by refl) (by refl) a_is_global)
))

#eval mclp_to_program arrcp₁
#eval mclp_to_program arrcp₂
--#reduce mclp_to_program arrcp₂

example (c) : mclp_to_program arrcp₁ = c := begin
    rw arrcp₁,
    rw [mclp_to_program, mclk_to_kernel, prepend_load_expr, load_global_vars_for_expr],
    repeat {rw list.append},
    repeat {rw list.foldl},
    repeat {rw list.foldr},
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

example : mclp_rel eq arrcp₁ arrcp₂ eq := begin
    apply rel_mclk_to_mclp,
end

end arrcp_mcl -/