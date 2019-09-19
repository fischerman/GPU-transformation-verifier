import parlang.defs

open parlang

section

variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

/-- syncable with the exception that no thread is allowed to store 
or load in stores and loads respectively. Adding to stores or load makes this property stricter -/
def syncable' (shole : set ι) (lhole : set ι) (s : state n σ τ) (m : memory τ) : Prop :=
state.syncable s m ∧
(∀ i tid, (i ∈ shole → i ∉ (s.threads.nth tid).stores) ∧
        (i ∈ lhole → i ∉ (s.threads.nth tid).loads))

lemma syncable_syncable' (s : state n σ τ) (m : memory τ) : syncable' ∅ ∅ s m ↔ state.syncable s m := begin
    unfold syncable',
    simp,
end



end