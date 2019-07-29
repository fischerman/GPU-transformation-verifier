import mcl.defs
import mcl.rhl
import mcl.compute_list

open parlang
open parlang.state
open parlang.thread_state
open mcl
open mcl.rhl

inductive op (sig : signature)
| store {t} {dim} (var : string) (idx : vector (expression sig type.int) dim) (h₁ : type_of (sig.val var) = t) (h₂ : ((sig.val var).type).dim = dim) : op
| compute_list (computes : list (memory (parlang_mcl_tlocal sig) → memory (parlang_mcl_tlocal sig))) : op

def ts_updates {sig : signature} : list (op sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)
| [] ts := ts
| (op.store var idx h₁ h₂ :: ops) ts := ts_updates ops $ mcl_store var idx h₁ h₂ ts
| (op.compute_list computes :: ops) ts := ts_updates ops $ compute_list computes ts

lemma ts_update_compute_list {sig : signature} (ups : list (op sig)) (computes) : ts_updates (op.compute_list computes :: ups) = ts_updates ups ∘ compute_list computes := by refl

lemma ts_update_split {sig : signature} (up) (ups : list (op sig)) : ts_updates (list.reverse (up :: ups)) = ts_updates [up] ∘ ts_updates (list.reverse ups) := begin
    funext ts,
    rw list.reverse_cons,
    induction (list.reverse ups) generalizing ts,
    {
        refl,
    }, {
        simp,
        cases hd;
        rw ts_updates;
        apply ih,
    }
end

lemma ts_updates_tlocal {sig : signature}  {ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} {updates} (m loads stores) : 
(ts_updates updates ts).tlocal = (ts_updates updates { tlocal := ts.tlocal, loads := loads, stores := stores, global := m }).tlocal := begin
    sorry,
end

lemma ts_updates_nil {sig : signature} (f : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)) : 
ts_updates [] ∘ f = f := begin
    refl,
end

@[simp]
lemma ts_updates_store {sig : signature} {dim} {idx : vector (expression sig type.int) dim} {var t} {h₁ : type_of (sig.val var) = t} {h₂} {updates} (f : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)) : 
ts_updates updates ∘ mcl_store var idx h₁ h₂ ∘ f = ts_updates (op.store var idx h₁ h₂ :: updates) ∘ f := begin
    refl,
end

@[simp]
lemma ts_updates_compute {sig : signature} {g} {updates} (f : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)) : 
ts_updates updates ∘ compute g ∘ f = ts_updates (op.compute_list [g] :: updates) ∘ f := begin
    refl,
end

@[simp]
lemma ts_updates_merge_computes_list {sig : signature} {updates} {com com' : list (memory (parlang_mcl_tlocal sig) → memory (parlang_mcl_tlocal sig))} :
ts_updates (op.compute_list com :: op.compute_list com' :: updates) = ts_updates (op.compute_list (com ++ com') :: updates) := begin
    sorry,
end

@[simp]
lemma compute_list_stores' {sig : signature} {n} {tid : fin n} {ac : vector bool n} {computes}
{s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} : 
(vector.nth ((map_active_threads ac (ts_updates [op.compute_list computes]) s).threads) tid).stores = (vector.nth s.threads tid).stores := begin
    by_cases h : ac.nth tid = tt,
    {
        simp [ts_updates, map_active_threads_nth_ac h],
    }, {
        rw ←map_active_threads_nth_inac h,
    }
end

@[simp]
lemma compute_list_loads' {sig : signature} {n} {tid : fin n} {ac : vector bool n} {computes}
{s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} : 
(vector.nth ((map_active_threads ac (ts_updates [op.compute_list computes]) s).threads) tid).loads = (vector.nth s.threads tid).loads := begin
    by_cases h : ac.nth tid = tt,
    {
        simp [ts_updates, map_active_threads_nth_ac h],
    }, {
        rw ←map_active_threads_nth_inac h,
    }
end

@[simp]
lemma compute_list_shared' {sig : signature} {n} {tid : fin n} {ac : vector bool n} {computes}
{s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} : 
(vector.nth ((map_active_threads ac (ts_updates [op.compute_list computes]) s).threads) tid).global = (vector.nth s.threads tid).global := begin
    by_cases h : ac.nth tid = tt,
    {
        simp [ts_updates, map_active_threads_nth_ac h],
    }, {
        rw ←map_active_threads_nth_inac h,
    }
end