import mcl
import mcl_rhl
import parlang
import syncablep
import use_cases.assign_mcl

open mcl
open mcl.mclk
open mcl.rhl
open parlang
open parlang.state
open parlang.thread_state
open assign_mcl

namespace assign_mcl

def sigc : signature_core
| "tid" := { scope := scope.tlocal, type := ⟨1, type.int⟩ }
| _ := { scope := scope.global, type := ⟨1, type.int⟩ }

def sig : signature := ⟨sigc, begin
    split,
    refl,
    refl,
end⟩

lemma a_is_global : is_global (sig.val "a") := by apply eq.refl
lemma tid_is_tlocal : is_tlocal (sig.val "tid") := by apply eq.refl

-- TODO generate those proofs directly from signature
-- make type classes out of those
-- make name explicit in state.update
def read_tid := (expression.tlocal_var "tid" (λ_, 0) (show type_of (sig.val "tid") = type.int, by apply eq.refl) (show (sig.val "tid").type.dim = 1, by apply eq.refl) tid_is_tlocal)

instance : has_one (expression sig (type_of (sig.val "b"))) := begin
    have : type_of (sig.val "b") = type.int := by apply eq.refl,
    rw this,
    apply_instance,
end

def p₁ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "a" v[read_tid] (by refl) (by refl) read_tid ;;
    mclk.global_assign "b" v[read_tid] (by refl) (by refl) (read_tid + (expression.literal_int 1 (by refl)))
)

def p₂ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "b" v[read_tid] (by refl) (by refl) (read_tid + (expression.literal_int 1 (by refl))) ;;
    mclk.global_assign "a" v[read_tid] (by refl) (by refl) read_tid
)

end assign_mcl