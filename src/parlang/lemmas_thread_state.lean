import parlang.defs

namespace parlang
namespace thread_state
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]



lemma store_accesses {ts : thread_state σ τ} {i} : i ∉ accesses ts → i ∉ stores ts := begin
  unfold accesses,
  rw [set.mem_union, not_or_distrib],
  intros h,
  cases h,
  trivial,
end

lemma loads_accesses {ts : thread_state σ τ} {i} : i ∉ accesses ts → i ∉ loads ts := begin
  unfold accesses,
  rw [set.mem_union, not_or_distrib],
  intro h,
  cases h,
  trivial,
end

@[simp]
lemma compute_id : @thread_state.compute σ _ τ _ id = id := begin
  funext ts,
  cases ts,
  simp [thread_state.compute],
end

#print store._match_1

lemma store_intro (f : σ → (Σi:ι, τ i)) (t : thread_state σ τ) : store f t = { shared := t.shared.update (f t.tlocal).1 (f t.tlocal).2,
  stores := insert (f t.tlocal).1 t.stores,
  .. t} := begin
  sorry,
end

/-- TODO: rename to store_compute_comm -/
lemma thread_state_map {f : thread_state σ τ → thread_state σ τ} {g h} : f ∘ thread_state.store g ∘ thread_state.compute h = f ∘ thread_state.compute h ∘ thread_state.store (λ s, g (h s)) := begin
  funext,
  simp,
  unfold compute,
  cases x,
  rw store_intro,
  rw store_intro,
end

/-- TODO: rename to store_compute_comm' -/
lemma thread_state_map' {g : σ → Σ (i : ι), τ i} {h} : thread_state.store g ∘ thread_state.compute h = thread_state.compute h ∘ thread_state.store (λ s, g (h s)) := begin
  funext,
  simp,
  unfold compute,
  cases x,
  rw store_intro,
  rw store_intro,
end

end thread_state
end parlang