import mcl
import parlang
open mcl
open mcl.mclk

namespace assign_mcl

def sig : signature
| "tid" := { scope := scope.tlocal, type := ⟨_, [1], type.int⟩ }
| _ := { scope := scope.global, type := ⟨_, [100], type.int⟩ }

lemma a_is_global : is_global (sig "a") := by apply eq.refl
lemma tid_is_tlocal : is_tlocal (sig "tid") := by apply eq.refl

def read_tid := (expression.tlocal_var "tid" (λ_, 0) (show type_of (sig "tid") = type.int, by apply eq.refl) (show (sig "tid").type.dim = 1, by apply eq.refl) tid_is_tlocal)

instance : has_one (expression sig (type_of (sig "b"))) := begin
    have : type_of (sig "b") = type.int := by apply eq.refl,
    rw this,
    apply_instance,
end

def p₁ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "a" [read_tid] (by refl) read_tid ;;
    mclk.global_assign "b" [read_tid] (by refl) (read_tid + 1)
)

def p₂ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "b" [read_tid] (by refl) (read_tid + 1) ;;
    mclk.global_assign "a" [read_tid] (by refl) read_tid
)

example : mclp_rel eq p₁ p₂ eq := begin
    apply rel_mclk_to_mclp,
end

end assign_mcl