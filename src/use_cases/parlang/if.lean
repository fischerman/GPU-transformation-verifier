import parlang

namespace parlang

example {σ₁ ι₁ ι₂ : Type} {τ₁ : ι₁ → Type} {τ₂ : ι₂ → Type} [decidable_eq ι₁] [decidable_eq ι₂] : 
{* λ n₁ s₁ ac₁ n₂ (s₂ : state n₂ (memory (λ (n: string), ℕ)) τ₂) ac₂, all_threads_active ac₂ ∧ 0 < n₂ *} 
@kernel.compute ι₁ σ₁ τ₁ id ~> kernel.ite (λm, m.get "tid" = 1) (kernel.compute (λ m, m.update "x" 1)) (kernel.compute (λm, m.update "x" 0)) 
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, ∀ (h : 0 < n₂), (s₂.threads.nth ⟨0, h⟩).tlocal.get "x" = 1 *} := begin
    apply if_right,
    swap 3,
    exact (λn₁ s₁ ac₁ n₂ s₂ ac₂, ∀ (h : 0 < n₂), (s₂.threads.nth ⟨0, h⟩).tlocal.get "x" = 1),
    {
        apply consequence_pre,
        apply compute_right,
        intros _ _ _ _ _ _ hp _,
        rw state.map_active_threads_nth_ac,
        refl,
        sorry,
    }, {
        apply consequence_pre,
        apply compute_right,
        intros _ _ _ _ _ _ hp _,
        rw ← state.map_active_threads_nth_inac,
        exact hp.left h,
        sorry,
    }
end

example {σ₁ ι₁ ι₂ : Type} {τ₁ : ι₁ → Type} {τ₂ : ι₂ → Type} [decidable_eq ι₁] [decidable_eq ι₂] : 
{* λ n₁ s₁ ac₁ n₂ (s₂ : state n₂ (memory (λ (n: string), ℕ)) τ₂) ac₂, all_threads_active ac₂ ∧ 0 < n₂ *} 
@kernel.compute ι₁ σ₁ τ₁ id ~> kernel.ite (λm, m.get "tid" = 1) (kernel.compute (λ m, m.update "x" 1)) (kernel.compute (λm, m.update "x" 0)) 
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, ∀ (h : 0 < n₂), (s₂.threads.nth ⟨0, h⟩).tlocal.get "x" = 1 *} := begin
    
end

end parlang