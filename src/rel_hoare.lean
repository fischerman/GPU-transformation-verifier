import parlang

namespace parlang

variables {σ σ₁ σ₂ : Type} {ι : Type} {τ τ₁ τ₂ : ι → Type} [decidable_eq ι]

-- we assume the same type ι for addressing global memory
def rel_hoare_state (P : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop) (k₁ : kernel σ₁ τ₁) (k₂ : kernel σ₂ τ₂) 
    (Q : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop) : Prop :=
    ∀ (n₁ n₂ : ℕ) (s₁ s₁' : state n₁ σ₁ τ₁) (s₂ : state n₂ σ₂ τ₂) ac₁ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → exec_state k₁ ac₁ s₁ s₁' →
    ∃ s₂', exec_state k₂ ac₂ s₂ s₂' ∧ Q n₁ s₁' ac₁ n₂ s₂' ac₂

notation `{* ` P : 1 ` *} ` k₁ : 1 ` ~ ` k₂ : 1 ` {* ` Q : 1 ` *}` := rel_hoare_state P k₁ k₂ Q

def rel_hoare_memory (P : memory τ → memory τ → Prop) (k₁ : kernel σ τ) (k₂ : kernel σ τ) (Q : memory τ → memory τ → Prop) :=
∀ (n₁ n₂) s (ac₁ : vector bool n₁) (ac₂ : vector bool n₂) m m' o, P m m' → exec_memory k₁ ac₁ s m o → ∃ u o', exec_memory k₂ ac₂ u m' o' → Q o o'


namespace rel_hoare

-- lemma seq {P Q R} {k₁ k₁' k₂ k₂' : kernel σ τ} : {* P *} k₁ ~ k₁' {* Q *} → {* Q *} k₂ ~ k₂' {* R *} → {* P *} (k₁ ;; k₂) ~ (k₁' ;; k₂') {* R *} := begin
--     intros h₁ h₂ n s u ac m m' o o' hp hseq₁ hseq₂,
--     cases hseq₁,
--     cases hseq₂,
--     cases hseq₁_hk,
--     cases hseq₂_hk,
--     unfold rel_hoare at h₁ h₂,
--     apply h₂ n _ _ _ _ _ _ _ _ _ hseq₁_hk_a_1 hseq₂_hk_a_1,
-- end

end rel_hoare

def rel_hoare_program (init₁ : ℕ → σ₁) (init₂ : ℕ → σ₂) (P : memory τ₁ → memory τ₂ → Prop) (p₁ : program σ₁ τ₁) (p₂ : program σ₂ τ₂) (Q : memory τ₁ → memory τ₂ → Prop) := 
∀ m₁ m₁' m₂, P m₁ m₂ → exec_prog init₁ p₁ m₁ m₁' → ∃ m₂', exec_prog init₂ p₂ m₂ m₂' ∧ Q m₁' m₂'

-- notation `{* ` P : 1 ` *} ` p₁ : 1 ` ~ ` p₂ : 1 ` {* ` Q : 1 ` *}` := rel_hoare_state P p₁ p₂ Q

lemma rel_kernel_to_program (k₁ : kernel σ₁ τ₁) (k₂ : kernel σ₂ τ₂) (init₁ : ℕ → σ₁) (init₂ : ℕ → σ₂) (P Q : memory τ₁ → memory τ₂ → Prop) (f₁ : memory τ₁ → ℕ) (f₂ : memory τ₂ → ℕ)
 (h : {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, ∃ m₁ m₂, s₁.syncable m₁ ∧ s₂.syncable m₂ ∧ n₁ = f₁ m₁ ∧ n₂ = f₂ m₂ ∧
 (∀ i : fin n₁, (s₁.threads.nth i).tlocal = init₁ i) ∧ (∀ i : fin n₂, (s₂.threads.nth i).tlocal = init₂ i) ∧ 
 P m₁ m₂ ∧ all_threads_active ac₁ ∧ all_threads_active ac₂ *} k₁ ~ k₂ 
 {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, ∃ m₁ m₂, s₁.syncable m₁ ∧ s₂.syncable m₂ ∧ Q m₁ m₂ *} ) : -- if I have to proof syncability of s₁, do I really have to assume termination of the left?
 rel_hoare_program init₁ init₂ P (program.intro f₁ k₁) (program.intro f₂ k₂) Q :=
begin
    unfold rel_hoare_state at h,
    unfold rel_hoare_program,
    intros m₁ m₁' m₂ hp hep,
    cases hep,
    specialize h (f₁ m₁) (f₂ m₂) 
        (init_state init₁ f₁ m₁)
        hep_s'
        (init_state init₂ f₂ m₂)
        (vector.repeat tt (f₁ m₁))
        (vector.repeat tt (f₂ m₂)),
    have hh : (∃ (s₂' : state (f₂ m₂) σ₂ τ₂), exec_state k₂ (vector.repeat tt (f₂ m₂)) (init_state init₂ f₂ m₂) s₂' ∧
    ∃ (m₁_1 : memory τ₁) (m₂_1 : memory τ₂), state.syncable hep_s' m₁_1 ∧ state.syncable s₂' m₂_1 ∧ Q m₁_1 m₂_1) := begin
        apply h,
        {
            apply exists.intro m₁,
            apply exists.intro m₂,
            apply and.intro,
            {
                apply init_state_syncable,
            }, {
                apply and.intro,
                {
                    apply init_state_syncable,
                },
                {
                    apply and.intro,
                    {
                        refl,
                    },
                    {
                        apply and.intro,
                        {
                            refl,
                        },
                        {
                            apply and.intro,
                            {
                                simp,
                                intro i,
                                rw vector.range_nth,
                            },
                            {
                                apply and.intro,
                                {
                                    simp,
                                    intro i,
                                    rw vector.range_nth,
                                }, {
                                    apply and.intro,
                                    {
                                        exact hp,
                                    }, {
                                        apply and.intro,
                                        {
                                            apply all_threads_active_repeat,
                                        }, {
                                            apply all_threads_active_repeat,
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }, {
            exact hep_he,
        }
    end,
    cases hh,
    cases hh_h,
    cases hh_h_right with m₁'',
    cases hh_h_right_h with m₂',
    apply exists.intro m₂',
    apply and.intro,
    {
        apply exec_prog.intro _ _ _ _ _ hh_w,
        { exact hh_h_right_h_h.right.left, },
        { exact hh_h_left, },
    }, {
        have hu : m₁' = m₁'' := begin
            by_cases hz : 0 < (f₁ m₁),
            {
                apply state.syncable_unique hep_hsync hh_h_right_h_h.left hz,
            }, {
                sorry
            }
        end,
        subst hu,
        exact hh_h_right_h_h.right.right,
    }
end

lemma single_step_left {P Q f} {k₁ : kernel σ₁ τ₁} {k₂ : kernel σ₂ τ₂} (R)
    (h : {* P *} (kernel.load f) ~ (kernel.compute id) {* R *})
    (h : {* R *} k₁ ~ k₂ {* Q *}) : 
    {* P *} (kernel.load f ;; k₁) ~ k₂ {* Q *} := begin
    sorry
end

end parlang