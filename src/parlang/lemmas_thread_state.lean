import parlang.def

namespace parlang
namespace thread_state
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]



lemma store_accesses {ts : thread_state σ τ} {i} : i ∉ accesses ts → i ∉ stores ts := sorry

lemma loads_accesses {ts : thread_state σ τ} {i} : i ∉ accesses ts → i ∉ loads ts := sorry

@[simp]
lemma compute_id : @thread_state.compute σ _ τ _ id = id := begin
  funext ts,
  cases ts,
  simp [thread_state.compute],
end

/-- TODO: rename to store_compute_comm -/
lemma thread_state_map {f : thread_state σ τ → thread_state σ τ} {g h} : f ∘ thread_state.store g ∘ thread_state.compute h = f ∘ thread_state.compute h ∘ thread_state.store (λ s, g (h s)) := by sorry

/-- TODO: rename to store_compute_comm' -/
lemma thread_state_map' {g : σ → Σ (i : ι), τ i} {h} : thread_state.store g ∘ thread_state.compute h = thread_state.compute h ∘ thread_state.store (λ s, g (h s)) := by sorry

end thread_state
end parlang