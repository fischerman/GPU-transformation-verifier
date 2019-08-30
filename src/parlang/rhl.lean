import parlang.defs
import parlang.lemmas_state
import parlang.lemmas_exec

namespace parlang

variables {σ σ₁ σ₂ σ₃ : Type} {ι₁ ι₂ : Type} {τ₁ : ι₁ → Type} {τ₂ : ι₂ → Type} [decidable_eq ι₁] [decidable_eq ι₂]

/-- Relational Hoare logic on kernels.  -/
def rel_hoare_state (P : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop) (k₁ : kernel σ₁ τ₁) (k₂ : kernel σ₂ τ₂) 
    (Q : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop) : Prop :=
    ∀ (n₁ n₂ : ℕ) (s₁ s₁' : state n₁ σ₁ τ₁) (s₂ : state n₂ σ₂ τ₂) ac₁ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → exec_state k₁ ac₁ s₁ s₁' →
    ∃ s₂', exec_state k₂ ac₂ s₂ s₂' ∧ Q n₁ s₁' ac₁ n₂ s₂' ac₂

notation `{* ` P : 1 ` *} ` k₁ : 1 ` ~> ` k₂ : 1 ` {* ` Q : 1 ` *}` := rel_hoare_state P k₁ k₂ Q

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

def initial_kernel_assertion (init₁ : ℕ → σ₁) (init₂ : ℕ → σ₂) (P : memory τ₁ → memory τ₂ → Prop) 
(f₁ : memory τ₁ → ℕ) (f₂ : memory τ₂ → ℕ) (m₁ : memory τ₁) (m₂ : memory τ₂) 
(n₁) (s₁ : state n₁ σ₁ τ₁) (ac₁ : vector bool n₁) (n₂) (s₂ : state n₂ σ₂ τ₂) (ac₂ : vector bool n₂) := 
s₁.syncable m₁ ∧ s₂.syncable m₂ ∧ n₁ = f₁ m₁ ∧ n₂ = f₂ m₂ ∧
(∀ i : fin n₁, s₁.threads.nth i = { tlocal := init₁ i, shared := m₁, stores := ∅, loads := ∅ }) ∧ 
(∀ i : fin n₂, s₂.threads.nth i = { tlocal := init₂ i, shared := m₂, stores := ∅, loads := ∅ }) ∧
P m₁ m₂ ∧ all_threads_active ac₁ ∧ all_threads_active ac₂

def initial_kernel_assertion_left_thread_state {init₁ : ℕ → σ₁} {init₂ : ℕ → σ₂} {P : memory τ₁ → memory τ₂ → Prop} 
{f₁ : memory τ₁ → ℕ} {f₂ : memory τ₂ → ℕ} {m₁ : memory τ₁} {m₂ : memory τ₂} 
{n₁} {s₁ : state n₁ σ₁ τ₁} {ac₁ : vector bool n₁} {n₂} {s₂ : state n₂ σ₂ τ₂} {ac₂ : vector bool n₂}
(i : initial_kernel_assertion init₁ init₂ P f₁ f₂ m₁ m₂ n₁ s₁ ac₁ n₂ s₂ ac₂) := i.right.right.right.right.left

#check initial_kernel_assertion_left_thread_state

def initial_kernel_assertion.right_thread_state {init₁ : ℕ → σ₁} {init₂ : ℕ → σ₂} {P : memory τ₁ → memory τ₂ → Prop} 
{f₁ : memory τ₁ → ℕ} {f₂ : memory τ₂ → ℕ} {m₁ : memory τ₁} {m₂ : memory τ₂} 
{n₁} {s₁ : state n₁ σ₁ τ₁} {ac₁ : vector bool n₁} {n₂} {s₂ : state n₂ σ₂ τ₂} {ac₂ : vector bool n₂}
(i : initial_kernel_assertion init₁ init₂ P f₁ f₂ m₁ m₂ n₁ s₁ ac₁ n₂ s₂ ac₂) := i.right.right.right.right.right.left


def initial_kernel_assertion.left_all_threads_active {init₁ : ℕ → σ₁} {init₂ : ℕ → σ₂} {P : memory τ₁ → memory τ₂ → Prop} 
{f₁ : memory τ₁ → ℕ} {f₂ : memory τ₂ → ℕ} {m₁ : memory τ₁} {m₂ : memory τ₂} 
{n₁} {s₁ : state n₁ σ₁ τ₁} {ac₁ : vector bool n₁} {n₂} {s₂ : state n₂ σ₂ τ₂} {ac₂ : vector bool n₂}
(i : initial_kernel_assertion init₁ init₂ P f₁ f₂ m₁ m₂ n₁ s₁ ac₁ n₂ s₂ ac₂) := i.right.right.right.right.right.right.right.left

def initial_kernel_assertion.precondition {init₁ : ℕ → σ₁} {init₂ : ℕ → σ₂} {P : memory τ₁ → memory τ₂ → Prop} 
{f₁ : memory τ₁ → ℕ} {f₂ : memory τ₂ → ℕ} {m₁ : memory τ₁} {m₂ : memory τ₂} 
{n₁} {s₁ : state n₁ σ₁ τ₁} {ac₁ : vector bool n₁} {n₂} {s₂ : state n₂ σ₂ τ₂} {ac₂ : vector bool n₂}
(i : initial_kernel_assertion init₁ init₂ P f₁ f₂ m₁ m₂ n₁ s₁ ac₁ n₂ s₂ ac₂) := i.right.right.right.right.right.right.left

#check initial_kernel_assertion.left_all_threads_active

lemma initial_kernel_assertion.initial_state_eq {init₁ : ℕ → σ₁}
{f₁ : memory τ₁ → ℕ} {f₂ : memory τ₁ → ℕ} {m₁ : memory τ₁} {m₂ : memory τ₁} 
{n₁} {s₁ : state n₁ σ₁ τ₁} {ac₁ : vector bool n₁} {s₂ : state n₁ σ₁ τ₁} {ac₂ : vector bool n₁} :
initial_kernel_assertion init₁ init₁ eq f₁ f₂ m₁ m₂ n₁ s₁ ac₁ n₁ s₂ ac₂ →
s₁ = s₂ |
(and.intro _ (and.intro _ (and.intro _ (and.intro _ (and.intro s_eq (and.intro s'_eq _)))))) := begin
    clear initial_kernel_assertion.initial_state_eq,
    cases s₁,
    cases s₂,
    simp,
    apply vector.eq_element_wise,
    intro tid,
    simp *,
end

lemma rel_kernel_to_program {k₁ : kernel σ₁ τ₁} {k₂ : kernel σ₂ τ₂} {init₁ : ℕ → σ₁} {init₂ : ℕ → σ₂} {P Q : memory τ₁ → memory τ₂ → Prop} {f₁ : memory τ₁ → ℕ} {f₂ : memory τ₂ → ℕ}
 (h : {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, ∃ m₁ m₂, initial_kernel_assertion init₁ init₂ P f₁ f₂ m₁ m₂ n₁ s₁ ac₁ n₂ s₂ ac₂ *} k₁ ~> k₂ 
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

lemma single_step_left {P Q} {k₁ k : kernel σ₁ τ₁} {k₂ : kernel σ₂ τ₂} (R)
    (h₁ : {* P *} k ~> (kernel.compute id) {* R *})
    (h₂ : {* R *} k₁ ~> k₂ {* Q *}) : 
    {* P *} (k ;; k₁) ~> k₂ {* Q *} := begin
    intros n₁ n₂ s₁ s₁'' s₂ ac₁ ac₂ hp hek₁,
    cases hek₁,
    specialize h₁ n₁ n₂ s₁ _ s₂ ac₁ ac₂ hp hek₁_a,
    cases h₁ with s₂' h₁,
    cases h₁,
    have : s₂ = s₂' := begin
        cases h₁_left,
        cases s₂,
        sorry, -- trivial
    end,
    apply h₂,
    rw this,
    exact h₁_right,
    exact hek₁_a_1,
end

variables {P Q R P' Q' : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop} {k₁ k₁' : kernel σ₁ τ₁} {k₂ k₂' : kernel σ₂ τ₂}

-- intuition of the proof (to be repurposed by further proofs):
-- we get the intermediate state of after k₁ by cases
-- from h₁ we get state after k₂
-- from h₂ we get state after k₂'
lemma seq (Q)
    (h₁ : {* P *} k₁ ~> k₂ {* Q *})
    (h₂ : {* Q *} k₁' ~> k₂' {* R *}) :
    {* P *} (k₁ ;; k₁') ~> (k₂ ;; k₂') {* R *} := begin
        intros _ _ _ _ _ _ _ hp hek₁k₁',
        cases hek₁k₁',
        specialize h₁ n₁ n₂ s₁ hek₁k₁'_t s₂ ac₁ ac₂ hp hek₁k₁'_a,
        cases h₁ with t₂,
        cases h₁_h with hek₂ hq,
        specialize h₂ n₁ n₂ hek₁k₁'_t _ t₂ ac₁ ac₂ hq hek₁k₁'_a_1,
        cases h₂ with s₂',
        apply exists.intro s₂',
        apply and.intro,
        apply exec_state.seq _ _ _ _ _ _ hek₂ (h₂_h.left),
        exact h₂_h.right,
end

-- sometimes called sub
lemma consequence (h : {* P *} k₁ ~> k₂ {* Q *}) 
(hp : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P' n₁ s₁ ac₁ n₂ s₂ ac₂ → P n₁ s₁ ac₁ n₂ s₂ ac₂)
(hq : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, Q n₁ s₁ ac₁ n₂ s₂ ac₂ → Q' n₁ s₁ ac₁ n₂ s₂ ac₂) : {* P' *} k₁ ~> k₂ {* Q' *} := begin
    intros _ _ _ _ _ _ _ hp' he₁,
    specialize h n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ _ he₁,
    cases h with s₂ h,
    use s₂,cases h,
    apply and.intro,
    assumption,
    apply hq,
    assumption,
    apply hp,
    assumption,
end

lemma consequence_pre (h : {* P *} k₁ ~> k₂ {* Q *}) 
(hp : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P' n₁ s₁ ac₁ n₂ s₂ ac₂ → P n₁ s₁ ac₁ n₂ s₂ ac₂) : 
{* P' *} k₁ ~> k₂ {* Q *} := begin
    apply consequence,
    exact h,
    exact hp,
    intros,
    exact a,
end

def assertion_swap_side (P : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop) := λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₂ s₂ ac₂ n₁ s₁ ac₁

#print assertion_swap_side

-- k₁ must terminate
lemma swap (h : {* P *} k₁ ~> k₂ {* Q *}) (he₁ : ∀ {n₁ s₁ ac₁ n₂ s₂ ac₂}, P n₁ s₁ ac₁ n₂ s₂ ac₂ → ∃ s₁', exec_state k₁ ac₁ s₁ s₁') : 
{* assertion_swap_side P *} k₂ ~> k₁ {* assertion_swap_side Q *} := begin
    intros n₂ n₁ s₂ s₂' s₁ ac₂ ac₁ hp he₂,
    simp,
    have : ∃ s₁', exec_state k₁ ac₁ s₁ s₁' := he₁ hp,
    cases this with s₁' he₂,
    use s₁',
    split,
    assumption,
    specialize h n₁ n₂ s₁ _ s₂ ac₁ ac₂ hp he₂,
    cases h,
    have : h_w = s₂' := sorry, -- by uniqueness
    subst this,
    exact h_h.right,
end

theorem trans (p₁ : program σ₁ τ₁) (p₂ : program σ₂ τ₁) (p₃ : program σ₃ τ₁) (init₁ init₂ init₃) (h₁ : rel_hoare_program init₁ init₂ eq p₁ p₂ eq) (h₂ : rel_hoare_program init₂ init₃ eq p₂ p₃ eq) :
rel_hoare_program init₁ init₃ eq p₁ p₃ eq := begin
    unfold rel_hoare_program at *,
    intros _ _ _ heq he,
    specialize h₁ m₁ m₁' m₂ heq he,
    cases h₁ with m h,
    cases h,
    subst heq,
    subst h_right,
    specialize h₂ m₁ m₁' m₁ rfl h_left,
    exact h₂,
end

theorem compute_right (f) : {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, Q n₁ s₁ ac₁ n₂ (s₂.map_active_threads ac₂ $ thread_state.compute f) ac₂ *} (kernel.compute id) ~> (kernel.compute f) {* Q *} := begin
    intros _ _ _ _ _ _ _ hp he,
    use (s₂.map_active_threads ac₂ $ thread_state.compute f),
    split,
    {
        apply exec_state.compute,
    }, {
        cases he,
        sorry, -- trivial
    }
end

theorem store_right (f : σ₂ → (Σ (i : ι₂), τ₂ i)) : 
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, Q n₁ s₁ ac₁ n₂ (s₂.map_active_threads ac₂ $ thread_state.store f) ac₂ *} 
(kernel.compute id) ~> (kernel.store f) 
{* Q *} := begin
    intros _ _ _ _ _ _ _ hp he,
    use (s₂.map_active_threads ac₂ $ thread_state.store f),
    split, {
        apply exec_state.store,
    }, {
        cases he,
        sorry, -- trivial
    }
end

lemma kernel_foldr_skip_right {k : kernel σ₂ τ₂} {ks} : 
{* P *} k₁ ~> list.foldr kernel.seq k ks {* Q *} ↔ {* P *} k₁ ~> list.foldr kernel.seq (kernel.compute id) ks ;; k {* Q *} := sorry

end parlang