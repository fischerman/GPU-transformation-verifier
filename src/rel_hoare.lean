import parlang

namespace parlang

variables {σ σ₁ σ₂ : Type} {ι : Type} {τ τ₁ τ₂ : ι → Type} [decidable_eq ι]

-- we assume the same type ι for addressing global memory
def rel_hoare_state (P : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop) (k₁ : kernel σ₁ τ₁) (k₂ : kernel σ₂ τ₂) 
    (Q : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop) : Prop :=
    ∀ (n₁ n₂ : ℕ) (s₁ s₁' : state n₁ σ₁ τ₁) (s₂ : state n₂ σ₂ τ₂) ac₁ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → exec_state k₁ ac₁ s₁ s₁' →
    ∃ s₂', exec_state k₂ ac₂ s₂ s₂' ∧ Q n₁ s₁' ac₁ n₂ s₂' ac₂

def rel_hoare_memory (P : memory τ → memory τ → Prop) (k₁ : kernel σ τ) (k₂ : kernel σ τ) (Q : memory τ → memory τ → Prop) :=
∀ (n₁ n₂) s (ac₁ : vector bool n₁) (ac₂ : vector bool n₂) m m' o, P m m' → exec_memory k₁ ac₁ s m o → ∃ u o', exec_memory k₂ ac₂ u m' o' → Q o o'

notation `{* ` P : 1 ` *} ` k₁ : 1 ` ~ ` k₂ : 1 ` {* ` Q : 1 ` *}` := rel_hoare_memory P k₁ k₂ Q

namespace rel_hoare

lemma seq {P Q R} {k₁ k₁' k₂ k₂' : kernel σ τ} : {* P *} k₁ ~ k₁' {* Q *} → {* Q *} k₂ ~ k₂' {* R *} → {* P *} (k₁ ;; k₂) ~ (k₁' ;; k₂') {* R *} := begin
    intros h₁ h₂ n s u ac m m' o o' hp hseq₁ hseq₂,
    cases hseq₁,
    cases hseq₂,
    cases hseq₁_hk,
    cases hseq₂_hk,
    unfold rel_hoare at h₁ h₂,
    apply h₂ n _ _ _ _ _ _ _ _ _ hseq₁_hk_a_1 hseq₂_hk_a_1,
end

end rel_hoare

def rel_hoare_program (init₁ : ℕ → σ₁) (init₂ : ℕ → σ₂) (P : memory τ₁ → memory τ₂ → Prop) (p₁ : program σ₁ τ₁) (p₂ : program σ₂ τ₂) (Q : memory τ₁ → memory τ₂ → Prop) := 
∀ m₁ m₁' m₂, P m₁ m₂ → exec_prog init₁ p₁ m₁ m₁' → ∃ m₂', exec_prog init₂ p₂ m₂ m₂' ∧ Q m₁' m₂'

end parlang