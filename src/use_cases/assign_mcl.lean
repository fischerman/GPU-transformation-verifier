import mcl.defs
import mcl.rhl
import parlang.defs
import syncablep
import mcl.compute_list
import mcl.ts_updates

open mcl
open mcl.mclk
open mcl.rhl

namespace assign_mcl

open parlang
open parlang.state
open parlang.thread_state

/- not in use -/
-- lemma store_access_elim_name {sig : signature} {n n_idx} {s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)} {var} {idx : vector (expression sig type.int) n_idx} 
-- {t h₄} {h₃ : type_of (sig.val var) = t } {f} {t : fin n} {i} {ac₁ : vector bool n} {updates}
-- (h₁ : i ∉ accesses (vector.nth ((map_active_threads ac₁ (f ∘ compute_list updates) s).threads) t)) 
-- (h₂ : i.1 ≠ var) :
-- i ∉ accesses (vector.nth ((map_active_threads ac₁ (f ∘ (thread_state.tlocal_to_shared var idx h₃ h₄) ∘ compute_list updates) s).threads) t) := begin
--     sorry,
-- end

-- lemma store_no_stores_name {sig : signature} {dim} {idx : vector (expression sig type.int) dim} {var t} {h₁ : type_of (sig.val var) = t} {h₂} {computes : list (memory (parlang_mcl_tlocal sig) → memory (parlang_mcl_tlocal sig))}
-- {ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)} {i : mcl_address sig}
-- {n} {s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)} {m : memory (parlang_mcl_shared sig)} {tid}
-- {f : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)} : 
-- syncable ((f ∘ compute_list computes) s) m →
-- i.fst ≠ var →
-- i ∉ ((f ∘ compute_list computes) (s.threads.nth tid)).stores →
-- i ∉ ((f ∘ thread_state.tlocal_to_shared var idx h₁ h₂ ∘ compute_list computes) (s.threads.nth tid)).stores := begin
--     intros syncable i_not_var i_not_in_f,
--     unfold parlang.state.syncable at syncable,
--     specialize syncable i,
--     cases ts,
--     induction computes,
--     {
--         simp [compute_list, thread_state.tlocal_to_shared, store],
--     }, {

--     }
-- end

end assign_mcl