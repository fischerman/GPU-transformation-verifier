import parlang

open parlang

section

variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

/-- syncable with the exception that no threads is allowed to store 
or load in stores and loads respectively -/
def syncable' (stores : list ι) (loads : list ι) (s : state n σ τ) (m : memory τ) : Prop :=
(∀i:ι,
    (∀ tid, i ∉ (s.threads.nth tid).stores ∧ m i = (s.threads.nth tid).global i) ∨
    (∃ tid, i ∈ (s.threads.nth tid).stores ∧ m i = (s.threads.nth tid).global i ∧
        (∀ tid', tid ≠ tid' → i ∉ (s.threads.nth tid').accesses))) ∧
(∀ i tid, i ∈ stores → i ∉ (s.threads.nth tid).stores) ∧
(∀ i tid, i ∈ loads → i ∉ (s.threads.nth tid).loads)

example (s : state n σ τ) (m : memory τ) : syncable' [] [] s m ↔ state.syncable s m := begin
    unfold syncable',
    simp,
    refl,
end



end