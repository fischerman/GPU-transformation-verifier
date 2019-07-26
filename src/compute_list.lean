import parlang
import mcl

open parlang
open parlang.state
open parlang.thread_state
open mcl

def compute_list {σ ι : Type} {τ : ι → Type} [decidable_eq ι] : list (σ → σ) → (thread_state σ τ → thread_state σ τ)
| (f :: tl) := compute_list tl ∘ @compute σ ι τ _ f
| [] := id

lemma compute_to_compute_list {σ ι : Type} {τ : ι → Type} [decidable_eq ι] (f : σ → σ) : @compute σ ι τ _ f = compute_list [f] := by refl

lemma compute_list_merge {σ ι : Type} {τ : ι → Type} [decidable_eq ι] (f g : list (σ → σ)) : 
(@compute_list σ ι τ _ g) ∘ compute_list f = compute_list (f ++ g) := begin
    induction f,
    case list.nil {
        simp [compute_list],
    }, {
        simp [compute_list],
        rw ← f_ih,
    }
end

lemma compute_list_accesses {sig : signature} {n} (s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)) (i) (computes) (tid) : 
i ∉ (compute_list computes (vector.nth (s.threads) tid)).accesses ↔ i ∉ (vector.nth (s.threads) tid).accesses := sorry

-- todo: rewrite to s = { tlocal := ... s.tlocal, ..s }
lemma compute_list_tlocal {sig : signature} {computes : list (memory (parlang_mcl_tlocal sig) → memory (parlang_mcl_tlocal sig))} {tlocal loads stores} {global : memory $ parlang_mcl_global sig} : 
compute_list computes {tlocal := tlocal, global := global, loads := loads, stores := stores} = 
{tlocal := computes.foldl (λ tl com, com tl) tlocal, global := global, loads := loads, stores := stores} := begin
    induction computes generalizing tlocal,
    {
        refl,
    }, {
        simp [compute_list, compute, computes_ih],
    }
end

@[simp]
lemma compute_list_stores_core {sig : signature} {computes}
{ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} : 
(compute_list computes ts).stores = ts.stores := begin
    induction computes generalizing ts,
    { simp [compute_list], },
    { cases ts, simp [compute_list, compute], rw computes_ih, },
end

@[simp]
lemma compute_list_loads_core {sig : signature} {computes}
{ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} : 
(compute_list computes ts).loads = ts.loads := begin
    induction computes generalizing ts,
    { simp [compute_list], },
    { cases ts, simp [compute_list, compute], rw computes_ih, },
end

@[simp]
lemma compute_list_shared {sig : signature} {computes}
{ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} : 
(compute_list computes ts).global = ts.global := begin
    induction computes generalizing ts,
    { simp [compute_list], },
    { cases ts, simp [compute_list, compute], rw computes_ih, },
end

lemma compute_list_stores {sig : signature} {computes}
{ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} {i : mcl_address sig} : 
i ∉ ts.stores ↔ i ∉ (compute_list computes ts).stores := by simp

lemma compute_list_loads {sig : signature} {computes}
{ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} {i : mcl_address sig} : 
i ∉ ts.loads ↔ i ∉ (compute_list computes ts).loads := by simp