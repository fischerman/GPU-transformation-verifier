import parlang

/- IDEA: try to remove the active map from the assertions -/

namespace parlang

open kernel

-- notation ac ` ⇃ ` c ` ◂ `  x:(foldr ` ◂ ` (h t, deactivate_threads c ac h) ac) := x
notation ac ` ⇃ ` c ` ◂ `  s := deactivate_threads c ac s

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
    apply ite_right,
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

def p₁ : program bool (λ (s : string), ℕ) :=
program.intro (λ_, 1) (
    compute (λ_, tt) ;;
    ite id (
        store (λ_, ⟨"a", 7⟩)
    ) (
        store (λ_, ⟨"a", 5⟩)
    )
)

def p₂ : program bool (λ (s : string), ℕ) :=
program.intro (λ_, 1) (
    compute (λ_, tt) ;;
    store (λ_, ⟨"a", 7⟩)
)

example : rel_hoare_program (λ_, ff) (λ_, ff) eq p₁ p₂ eq := begin
    apply rel_kernel_to_program,
    apply single_step_left,
    swap,
    apply single_step_right,
    swap,
    {
        apply known_branch_left,
        swap,
        {
            apply consequence,
            apply rhl_eq,
            swap,
            {intros,
            cases a_1 with m₁,
            use m₁,
            use m₁,
            split,
            assumption,
            cases a,
            subst a_left,
            specialize a_right rfl,
            cases a_right,
            subst a_right_left,
            split,
            exact a_1_h,
            refl,},
            intros,
            have : (∀ (tid : fin n₁), id ((vector.nth (s₁.threads) tid).tlocal) = tt) ∧ n₁ = n₂ ∧ ∀ h : n₁ = n₂, s₁ = (by rw h; exact s₂) ∧ ac₁ = (by rw h; exact ac₂) := a,
            exact this.right,
        },
        intros,
        exact a.left tid,
    },
    apply compute_right,
    {
        apply consequence_pre,
        apply swap (compute_right _),
        {
            intros,
            use s₁,
            apply exec_skip,
        }, {
            intros _ _ _ _ _ _ h,
            simp[assertion_swap_side],
            cases h with m₁ h,
            cases h with m₂ h,
            cases h with h₁ h,
            cases h with h₂ h,
            cases h with h₃ h,
            cases h with h₄ h,
            cases h with h₅ h,
            cases h with h₆ h,
            cases h with h₇ h,
            cases h with h₈ h₉,
            split,
            {
                intro tid,
                rw state.map_active_threads_nth_ac,
                refl,
                apply all_threads_active_nth h₈,
            }, 
            split,
            {
                subst h₇,
                rw [h₃, ← h₄],
            },
            intro h',
            subst h',
            split, {
                unfold state.map_active_threads,
                sorry, -- from initial
            }, {
                have : ac₁ = ac₂ := all_threads_active_eq h₈ h₉,
                exact this,
            }
        }
    }, {
        intros,
        sorry, -- trivial
    }
end

end parlang