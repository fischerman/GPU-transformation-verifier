import parlang

/- IDEA: try to remove the active map from the assertions -/

namespace parlang

example {σ₁ ι₁ ι₂ : Type} {τ₁ : ι₁ → Type} {τ₂ : ι₂ → Type} [decidable_eq ι₁] [decidable_eq ι₂] : 
{* λ n₁ s₁ ac₁ n₂ (s₂ : state n₂ (memory (λ (n: string), ℕ)) τ₂) ac₂, 0 < n₂ ∧ all_threads_active ac₂ *} 
@kernel.compute ι₁ σ₁ τ₁ id ~> kernel.ite (λm, m.get "tid" = 1) (kernel.compute (λ m, m.update "x" 1)) (kernel.compute (λm, m.update "x" 0)) 
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, ∀ (h : 0 < n₂), (s₂.threads.nth ⟨0, h⟩).tlocal.get "x" = 1 *} := begin
    suffices : {* λ n₁ s₁ ac₁ n₂ (s₂ : state n₂ (memory (λ (n: string), ℕ)) τ₂) ac₂, 0 < n₂ ∧ (λac₂, all_threads_active ac₂) ac₂ *} 
        @kernel.compute ι₁ σ₁ τ₁ id ~> kernel.ite (λm, m.get "tid" = 1) (kernel.compute (λ m, m.update "x" 1)) (kernel.compute (λm, m.update "x" 0)) 
    {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, (∀ (h : 0 < n₂), (s₂.threads.nth ⟨0, h⟩).tlocal.get "x" = 1) ∧ (λac₂, all_threads_active ac₂) ac₂ *},
    {
        apply consequence,
        exact this,
        simp,
        intros,
        exact ⟨a, a_1⟩,
        intros,
        exact (a.left) h,
    },
    apply if_right,
    swap 7,
    exact (λn₁ s₁ ac₁ n₂ s₂ ac₂, ∀ (h : 0 < n₂), (s₂.threads.nth ⟨0, h⟩).tlocal.get "x" = 1),
    {
        intros,
        simp *,
    }, {
        intros,
        exact a,
    }, {
        intros,
        exact a,
    }, {
        intros,
        exact a h,
    }, {
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

end parlang