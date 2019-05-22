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

-- TODO generate those proofs directly from signature
-- make type classes out of those
-- make name explicit in state.update
def read_tid := (expression.tlocal_var "tid" (λ_, 0) (show type_of (sig "tid") = type.int, by apply eq.refl) (show (sig "tid").type.dim = 1, by apply eq.refl) tid_is_tlocal)

instance : has_one (expression sig (type_of (sig "b"))) := begin
    have : type_of (sig "b") = type.int := by apply eq.refl,
    rw this,
    apply_instance,
end

def p₁ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "a" [read_tid] (by refl) (by refl) read_tid ;;
    mclk.global_assign "b" [read_tid] (by refl) (by refl) (read_tid + (expression.const_int 1 (by refl)))
)

def p₂ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "b" [read_tid] (by refl) (by refl) (read_tid + (expression.const_int 1 (by refl))) ;;
    mclk.global_assign "a" [read_tid] (by refl) (by refl) read_tid
)

open parlang
open parlang.state
open parlang.thread_state

#reduce update_global_vars_for_expr (read_tid + 1)

-- this approach is like computing both programs and comparing their output
-- this is a fairly naive approach, another approach would be to show that their behavior is equal (based on the fact that we have to show equality)
example : mclp_rel eq p₁ p₂ eq := begin
    apply rel_mclk_to_mclp,

    apply mcl.skip_right.mpr,
    apply mcl.seq,
    swap,

    apply mcl.skip_left_after.mpr,
    apply mcl.skip_right.mpr,
    apply mcl.seq,
    tactic.swap,

    -- break it down into individual proofs
    apply add_skip_left.mpr,
    apply mcl.seq,
    tactic.swap,
    {
        apply mcl.global_assign_right,
    },{
        apply mcl.global_assign_right,
    }, {
        apply mcl.global_assign_left,
    },
    apply mcl.global_assign_left',
    intros _ _ _ _ _ _ h,
    cases h with m₁ h,
    cases h with m₂ h,
    simp,
    have : n₁ = n₂ := begin
        sorry
    end,
    subst this,
    have hseq : s₁ = s₂ := begin
        sorry
    end,

    -- the proof obligation in the form of a map thread on syncable is the simple version because we never consider threads to change active state (here all threads are always active)

    -- h expresses the initial state (we might want to compress this information)
    -- todo: we need ways to reason about ranges of memory (dependent on tid, ergo n₁)
    -- e.g. using foldr
    apply exists.intro ((list.range n₁).foldl (λ (m : parlang.memory (parlang_mcl_global sig)) i, ((memory.update ("b", [i]) (i + 1 : ℕ) ∘ (memory.update ("a", [i]) i))) m) m₁),
    
    split, {
        have : update_global_vars_for_expr read_tid = id := by refl,
        rw this,
        have : update_global_vars_for_expr (read_tid + (expression.const_int 1 (show type_of (sig "b") = type_of (sig "b"), by refl))) = id := by refl,
        rw this,
        simp,

        -- put maps in store
        rw ← function.comp.assoc,
        rw ← function.comp.assoc,
        rw thread_state_map,
        rw ← function.comp.assoc,
        rw thread_state_map',
        rw function.comp.assoc,
        rw function.comp.assoc,
        rw syncable_remove_map,
        
        rw ← function.comp.assoc,
        rw thread_state_map',
        rw function.comp.assoc,
        rw syncable_remove_map,
        
        simp,
        -- resolve get and update (the result should only be mcl_init, literals and memory (in case of loads))
        -- only stores left
        -- find a way to resolve the stores all together
    }

end

end assign_mcl