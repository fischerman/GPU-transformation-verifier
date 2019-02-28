import parlang

namespace parlang

variables {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

def rel_hoare (P : memory τ → memory τ → Prop) (k₁ : kernel σ τ) (k₂ : kernel σ τ) (Q : memory τ → memory τ → Prop) :=
∀ (n) s u (ac : vector bool n) m m' o o', P m m'  → exec_memory k₁ ac s m o → exec_memory k₂ ac u m' o' → Q o o'

notation `{* ` P : 1 ` *} ` k₁ : 1 ` ~ ` k₂ : 1 ` {* ` Q : 1 ` *}` := rel_hoare P k₁ k₂ Q

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

end parlang