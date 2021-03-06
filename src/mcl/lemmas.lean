import mcl.defs
import mcl.rhl

open parlang
open mcl
open mcl.rhl
open parlang.thread_state

@[simp]
lemma store_stores {sig : signature} {dim} {idx : vector (expression sig type.int) dim} {var t} {h₁ : type_of (sig.val var) = t} {h₂}
{ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)} {i : mcl_address sig} : 
i ∉ (thread_state.tlocal_to_shared var idx h₁ h₂ ts).stores → i ∉ ts.stores := by simp [thread_state.tlocal_to_shared, store, not_or_distrib]

@[simp]
lemma store_loads {sig : signature} {dim} {idx : vector (expression sig type.int) dim} {var t} {h₁ : type_of (sig.val var) = t} {h₂}
{ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)} {i : mcl_address sig} : 
i ∉ (thread_state.tlocal_to_shared var idx h₁ h₂ ts).loads → i ∉ ts.loads := by simp [thread_state.tlocal_to_shared, store, not_or_distrib]

@[simp]
lemma array_hole_name_neq {sig : signature} (var₁ var₂ : string) (h : var₁ ≠ var₂) (idx : vector ℕ (((sig.val var₁).type).dim)) :
(⟨var₁, idx⟩ : mcl_address sig) ∉ @array_address_range sig var₂ := begin
    unfold array_address_range,
    intro,
    contradiction,
end