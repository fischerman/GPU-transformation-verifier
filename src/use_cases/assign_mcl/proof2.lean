import mcl.defs
import mcl.rhl
import mcl.compute_list
import mcl.ts_updates
import syncablep
import mcl.syncablep
import mcl.lemmas
import .defs

open mcl
open mcl.mclk
open mcl.rhl
open parlang
open parlang.state
open parlang.thread_state

namespace assign_mcl
namespace proof2

notation m ` & ` n ` ::= ` v := memory.update m n v
notation s ` § ` f ` ⇂ ` ac := map_active_threads ac f s

lemma assign_rel' : mclp_rel eq p₁ p₂ eq := begin
    apply rel_mclk_to_mclp,

    apply skip_right.mpr,
    apply rhl.seq,
    swap,

    apply skip_left_after.mpr,
    apply skip_right.mpr,
    apply rhl.seq,
    swap,

    -- break it down into individual proofs
    apply add_skip_left.mpr,
    apply rhl.seq,
    swap,
    {
        apply shared_assign_right,
    },{
        apply shared_assign_right,
    }, {
        apply shared_assign_left,
    },
    apply shared_assign_left',
    intros _ _ _ _ _ _ h,
    cases h with m₁ h,
    cases h with m₂ h,
    simp only [map_map_active_threads],
    have : n₁ = n₂ := begin
        sorry
    end,
    subst this,
    have hseq : s₁ = s₂ := begin
        sorry
    end,

    -- the proof obligation in the form of a map thread on syncable is the simple version because we never consider threads to change active state (here all threads are always active)

    -- the two updates store indepedently because "a" ≠ "b"
    -- the two updates read indepedently because they both depend on the same state (AFAIK they could still be swaped because the state is fixed)
    apply exists.intro _,
    apply exists.intro _,

    -- split up the proof for the individual memories
    split, {
        have : thread_state.update_shared_vars_for_expr read_tid = id := by refl,
        rw this,
        have : thread_state.update_shared_vars_for_expr (read_tid + (expression.literal_int 1 (show type_of (sig.val "b") = type_of (sig.val "b"), by refl))) = id := by refl,
        rw this,
        simp,

        -- resolve get and update (the result should only be mcl_init, literals and memory (in case of loads))
        rw ← syncable_syncable',
        rw function.comp.assoc,
        rw ← ts_updates_nil (thread_state.tlocal_to_shared _ _ _ _ ∘ _),
        rw [ts_updates_store, ts_updates_compute, ts_updates_store],
        rw [← function.comp.right_id (compute _)],
        rw [ts_updates_compute],
        rw [function.comp.right_id],
        apply syncable'_store (show ((sig.val "a").type).dim = 1, by refl),
        {
            simp,
        }, {
            simp,
        }, {
            intros tid₁ tid₂ hneq,
            simp [vector.map_cons],
            repeat { rw vector.map_nil },
            rw initial_kernel_assertion_left_thread_state h,
            rw initial_kernel_assertion_left_thread_state h,
            simp,
            rw ← vector.eq_one',
            intro a,
            cases tid₁,
            cases tid₂,
            have : tid₁_val = tid₂_val := begin
                apply a,
            end,
            subst this,
            contradiction,
        },
        rw ts_updates_merge_computes_list,
        apply syncable'_store (show ((sig.val "b").type).dim = 1, by refl),
        {
            intro idx,
            have : "b" ≠ "a" := by intro; cases a,
            simp [this],
        }, {
            intro idx,
            have : "b" ≠ "a" := by intro; cases a,
            simp [this],
        }, {
            intros tid₁ tid₂ hneq,
            simp [vector.map_cons],
            repeat { rw vector.map_nil },
            rw initial_kernel_assertion_left_thread_state h,
            rw initial_kernel_assertion_left_thread_state h,
            simp,
            rw ← vector.eq_one',
            intro a,
            cases tid₁,
            cases tid₂,
            have : tid₁_val = tid₂_val := begin
                apply a,
            end,
            subst this,
            contradiction,
        },
        simp [append, list.append],
        apply syncable'_compute_list_syncable,
        exact h.left,
        sorry, --trivial from h
        sorry, --trivial from h
    }, 
    split, {
        have : thread_state.update_shared_vars_for_expr read_tid = id := by refl,
        rw this,
        have : thread_state.update_shared_vars_for_expr (read_tid + (expression.literal_int 1 (show type_of (sig.val "b") = type_of (sig.val "b"), by refl))) = id := by refl,
        rw this,
        simp,

        -- resolve get and update (the result should only be mcl_init, literals and memory (in case of loads))
        rw ← syncable_syncable',
        rw function.comp.assoc,
        rw ← ts_updates_nil (thread_state.tlocal_to_shared _ _ _ _ ∘ _),
        rw [ts_updates_store, ts_updates_compute, ts_updates_store],
        rw [← function.comp.right_id (compute _)],
        rw [ts_updates_compute],
        rw [function.comp.right_id],
        apply syncable'_store (show ((sig.val "b").type).dim = 1, by refl),
        {
            simp,
        }, {
            simp,
        }, {
            intros tid₁ tid₂ hneq,
            simp [vector.map_cons],
            repeat { rw vector.map_nil },
            rw h.right_thread_state,
            rw h.right_thread_state,
            simp,
            rw ← vector.eq_one',
            intro a,
            cases tid₁,
            cases tid₂,
            have : tid₁_val = tid₂_val := begin
                apply a,
            end,
            subst this,
            contradiction,
        },
        rw ts_updates_merge_computes_list,
        apply syncable'_store (show ((sig.val "a").type).dim = 1, by refl),
        {
            intro idx,
            have : "a" ≠ "b" := by intro; cases a,
            simp [this],
        }, {
            intro idx,
            have : "a" ≠ "b" := by intro; cases a,
            simp [this],
        }, {
            intros tid₁ tid₂ hneq,
            simp [vector.map_cons],
            repeat { rw vector.map_nil },
            rw h.right_thread_state,
            rw h.right_thread_state,
            simp,
            rw ← vector.eq_one',
            intro a,
            cases tid₁,
            cases tid₂,
            have : tid₁_val = tid₂_val := begin
                apply a,
            end,
            subst this,
            contradiction,
        },
        simp [append, list.append],
        apply syncable'_compute_list_syncable,
        exact h.right.left,
        sorry, --trivial from h
        sorry, --trivial from h
    }, {
        -- show post-condition
        simp [append, list.append],
        rw ts_update_compute_list,
        rw from_tlocal_comm,
        have := h.precondition,
        subst this,
        have := h.initial_state_eq,
        subst this,
        apply from_tlocal_eq,
        {
            intro tid,
            rw map_active_threads_nth_ac,
            rw map_active_threads_nth_ac,
            refl,
            sorry, -- trivial
            sorry, -- trivial
        },
        apply from_tlocal_eq,
        {
            intro tid,
            rw map_active_threads_nth_ac,
            rw map_active_threads_nth_ac,
            refl,
            sorry, -- trivial
            sorry, -- trivial
        },
        refl,
    }
end

end proof2
end assign_mcl