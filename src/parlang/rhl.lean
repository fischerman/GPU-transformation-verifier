import parlang.defs
import parlang.lemmas_state
import parlang.lemmas_exec
import parlang.nonmono

namespace parlang

variables {σ σ₁ σ₂ σ₃ : Type} {ι₁ ι₂ : Type} {τ₁ : ι₁ → Type} {τ₂ : ι₂ → Type} [decidable_eq ι₁] [decidable_eq ι₂]

@[reducible]
def rhl_kernel_assertion := Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop

/-- Relational Hoare logic on kernels.  -/
def rel_hoare_state (P : rhl_kernel_assertion) (k₁ : kernel σ₁ τ₁) (k₂ : kernel σ₂ τ₂) 
    (Q : rhl_kernel_assertion) : Prop :=
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
 {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, (∃ m₁, s₁.syncable m₁) → ∃ m₁ m₂, s₁.syncable m₁ ∧ s₂.syncable m₂ ∧ Q m₁ m₂ *} )
 (hg : ∀ {m₁ m₂}, P m₁ m₂ → 0 < f₁ m₁) :
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
    ((∃ m₁, hep_s'.syncable m₁) → ∃ (m₁_1 : memory τ₁) (m₂_1 : memory τ₂), state.syncable hep_s' m₁_1 ∧ state.syncable s₂' m₂_1 ∧ Q m₁_1 m₂_1)) := begin
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
    specialize hh_h_right ⟨_, hep_hsync⟩,
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
            have hz : 0 < (f₁ m₁) := hg hp,
            apply state.syncable_unique hep_hsync hh_h_right_h_h.left hz,
        end,
        subst hu,
        exact hh_h_right_h_h.right.right,
    }
end

-- TODO: define the alias skip for (compute id)
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

variables {P Q R P' Q' I : Π n₁:ℕ, state n₁ σ₁ τ₁ → vector bool n₁ → Π n₂:ℕ, state n₂ σ₂ τ₂ → vector bool n₂ → Prop} {k₁ k₁' : kernel σ₁ τ₁} {k₂ k₂' : kernel σ₂ τ₂}

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

def assertion_swap_side (P : @rhl_kernel_assertion σ₁ σ₂ _ _ τ₁ τ₂ _ _) := λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₂ s₂ ac₂ n₁ s₁ ac₁

lemma swap' (h : {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ ∃ t, exec_state k₂ ac₂ s₂ t *} k₁ ~> k₂ {* Q *}) (he₁ : ∀ {n₁ s₁ ac₁ n₂ s₂ ac₂}, P n₁ s₁ ac₁ n₂ s₂ ac₂ → ∃ s₁', exec_state k₁ ac₁ s₁ s₁') : 
{* assertion_swap_side P *} k₂ ~> k₁ {* assertion_swap_side Q *} := begin
    sorry,
end

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

-- TODO: move to another file
theorem else_skip {n} (k : kernel σ τ₁) (c) (ac : vector bool n) (s s' : state n σ τ₁):
exec_state k (deactivate_threads (bnot ∘ c) ac s) s s' ↔ 
exec_state (kernel.ite c k (kernel.compute id)) ac s s' := begin
    split, {
        intro h,
        apply exec_state.ite s s',
        exact h,
        apply exec_skip,
    }, {
        intro h,
        cases h,
        have := eq.symm (exec_skip_eq h_a_1),
        subst this,
        exact h_a,
    }
end

-- we cannot prove that all threads are active after the else branch, because we cannot proof h₁ and h₂
-- maybe we have to make the active map explicitly available in the postcondition of ite, but how do we relate it the precondition? This is something that ghost variables would be for.

-- Q does not contain information about the pre-entry ac or state
/-- In the if-branch, the condition holds on all active threads. The inverse is not true. Just because the condition *c* holds, does not mean that the thread is active. -/
theorem ite_right (c : σ₂ → bool) (th) (el) (AC : ∀ {n₂ : ℕ}, vector bool n₂ → Prop)
(h₁ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → P n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂)) 
(h₂ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₂ σ₂ τ₂), Q n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s') → Q n₁ s₁ ac₁ n₂ s₂ ac₂)
(h₃ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₂ σ₂ τ₂), Q n₁ s₁ ac₁ n₂ s₂ ac₂ → Q n₁ s₁ ac₁ n₂ s₂ (deactivate_threads c ac₂ s')) 
(h₄ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₂ σ₂ τ₂), R n₁ s₁ ac₁ n₂ s₂ (deactivate_threads c ac₂ s') → R n₁ s₁ ac₁ n₂ s₂ ac₂) :
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₂.active_threads ac₂).all (λts, c ts.tlocal) *} kernel.compute id ~> th {* Q *} →
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, Q n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₂.active_threads ac₂).all (λts, bnot $ c ts.tlocal) *} kernel.compute id ~> el {* R *} →
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ AC ac₂ *} kernel.compute id ~> kernel.ite c th el {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, R n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ AC ac₂ *}
:= begin
    intros hth hel,
    intros _ _ _ _ _ _ _ hp he,
    specialize hth n₁ n₂ s₁ s₁ s₂ ac₁ (deactivate_threads (bnot ∘ c) ac₂ s₂) _ exec_skip,
    swap, {
        split, {
            apply h₁ _ _ _ _ _ _ hp.left,
        }, {
            sorry, -- not trivial
        }
    },
    cases hth with s₂' hth,
    specialize hel n₁ n₂ s₁ s₁ s₂' ac₁ (deactivate_threads c ac₂ s₂) _ (exec_skip),
    swap, {
        split, {
            apply h₃,
            apply h₂ _ _ _ _ _ _ s₂,
            exact hth.right,
        }, {
            sorry, -- not trivial
        }
    },
    cases hel with s₂'' hel,
    have := eq.symm (exec_skip_eq he),
    subst this,
    use s₂'',
    split, {
        apply exec_state.ite,
        exact hth.left,
        exact hel.left,
    }, 
    simp,
    split, {
        apply h₄,
        exact hel.right,
    }, {
        exact hp.right,
    }
end

/-- *ite_right* w/o an assertion on the active map -/
theorem ite_right' (c : σ₂ → bool) (th) (el)
(h₁ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → P n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂)) 
(h₂ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₂ σ₂ τ₂), Q n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s') → Q n₁ s₁ ac₁ n₂ s₂ ac₂)
(h₃ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₂ σ₂ τ₂), Q n₁ s₁ ac₁ n₂ s₂ ac₂ → Q n₁ s₁ ac₁ n₂ s₂ (deactivate_threads c ac₂ s')) 
(h₄ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₂ σ₂ τ₂), R n₁ s₁ ac₁ n₂ s₂ (deactivate_threads c ac₂ s') → R n₁ s₁ ac₁ n₂ s₂ ac₂) :
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₂.active_threads ac₂).all (λts, c ts.tlocal) *} kernel.compute id ~> th {* Q *} →
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, Q n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₂.active_threads ac₂).all (λts, bnot $ c ts.tlocal) *} kernel.compute id ~> el {* R *} →
{* P *} kernel.compute id ~> kernel.ite c th el {* R *}
:= begin
    intros _ _,
    suffices : {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (λ_, true) ac₂ *} kernel.compute id ~> kernel.ite c th el {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, R n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (λ_, true) ac₂ *},
    simp at this,
    exact this,
    apply ite_right,
    repeat { assumption, },
    exact h₂,
end

-- TODO: use ite_right
theorem then_right (c : σ₂ → bool) (th)
(h₁ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → P n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂)) 
(h₂ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s : state n₂ σ₂ τ₂), Q n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s) → Q n₁ s₁ ac₁ n₂ s₂ ac₂) :
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₂.active_threads ac₂).all (λts, c ts.tlocal) *} kernel.compute id ~> th {* Q *} →
{* P *} kernel.compute id ~> kernel.ite c th (kernel.compute id) {* Q *}
:= begin
    intros hth,
    intros _ _ _ _ _ _ _ hp he,
    have := eq.symm (exec_skip_eq he),
    subst this,
    specialize hth n₁ n₂ s₁ s₁ s₂ ac₁ (deactivate_threads (bnot ∘ c) ac₂ s₂) _ he,
    swap, {
        split, {
            apply h₁,
            apply hp,
        }, {
            sorry, -- not trivial
        }
    },
    cases hth with s₂' hth,
    use s₂',
    split, {
        apply exec_state.ite,
        exact hth.left,
        apply exec_skip,
    }, {
        apply h₂,
        apply hth.right,
    }
end

/-- TODO: 
    - add post-condition: condition is false on all active threads 
    - rename n
    - drop h₃ and deactivate threads in the post condition of hb ()
-/
/- theorem while_right.aux (c : σ₂ → bool) (k) (V : ∀ {n₂} (s₂ : state n₂ σ₂ τ₂) (ac₂ : vector bool n₂), ℕ)
(h₁ : ∀ {n₁ s₁ ac₁ n₂ s₂ ac₂}, P n₁ s₁ ac₁ n₂ s₂ ac₂ → P n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂)) 
(h₂ : ∀ {n₁ s₁ ac₁ n₂ s₂ ac₂} {s : state n₂ σ₂ τ₂}, P n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s) → P n₁ s₁ ac₁ n₂ s₂ ac₂)
(h₃ : ∀ {n₂} (s₂ : state n₂ σ₂ τ₂) (ac₂ : vector bool n₂), V s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂) ≤ V s₂ ac₂)
(hb : ∀ n, {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₂.active_threads ac₂).all (λts, c ts.tlocal) ∧ V s₂ ac₂ = n *} kernel.compute id ~> k {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ V s₂ ac₂ < n *}) :
∀ (n : ℕ), {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ V s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂) = n *} kernel.compute id ~> kernel.loop c k {* P *}
| n n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ ⟨hp, hv⟩ he := 
let ha := (any_thread_active (deactivate_threads (bnot ∘ c) ac₂ s₂)) in
let goal := ∃ (s₂' : state n₂ σ₂ τ₂), exec_state (kernel.loop c k) ac₂ s₂ s₂' ∧ P n₁ s₁' ac₁ n₂ s₂' ac₂ in
have base : ha = ff → goal, from begin
    intro ha,
    {
        use s₂,
        split, {
            apply exec_state.loop_stop,
            sorry
        }, {
            sorry, -- trivial
        }
    }
end,
have it : ha = tt → goal, from (
    assume hha,
    /- precondition holds in the first loop iteration -/
    have hp' : P n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂) := begin
        exact h₁ hp,
    end,
    /- the condition is true for all active threads in the first loop iteration -/
    have hc : list.all (state.active_threads (deactivate_threads (bnot ∘ c) ac₂ s₂) s₂) (λ ts , c (ts.tlocal)) = tt := begin
        sorry, -- not trivial
    end, 
    /- proof of first iteration -/
    have step : _ := hb (V s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂)) n₁ n₂ s₁ s₁ s₂ ac₁ (deactivate_threads (bnot ∘ c) ac₂ s₂) ⟨hp', ⟨hc, rfl⟩⟩ exec_skip,
    /- s₂' is the state after first iteration -/
    show goal, from match step with ⟨s₂', step⟩ :=
        /- condition holds after first iteration -/
        have hp'' : P n₁ s₁ ac₁ n₂ s₂' (deactivate_threads (bnot ∘ c) ac₂ s₂) := begin
            simp at step,
            exact step.right.left,
        end,
        have wf : V s₂' (deactivate_threads (bnot ∘ c) (deactivate_threads (bnot ∘ c) ac₂ s₂) s₂') < n := begin
            simp at step,
            subst hv,
            specialize h₃ s₂' (deactivate_threads (bnot ∘ c) ac₂ s₂),
            rw le_iff_eq_or_lt at h₃,
            cases h₃,
            {
                rw h₃,
                exact step.right.right,
            }, {
                apply lt_trans h₃ step.right.right,
            }
        end,
        have ih : _ := while_right.aux (V s₂' (deactivate_threads (bnot ∘ c) (deactivate_threads (bnot ∘ c) ac₂ s₂) s₂')) n₁ n₂ s₁ s₁ s₂' ac₁ (deactivate_threads (bnot ∘ c) ac₂ s₂) ⟨hp'', rfl⟩ exec_skip,
        show goal, from match ih with ⟨s₂'', ih⟩ := (begin
            use  s₂'',
            split, {
                apply exec_state.loop_step,
                exact ha,
                exact step.left,
                exact ih.left,
            }, {
                have := exec_skip_eq he,
                clear _match _match,
                subst this,
                apply h₂ ih.right,
            },
        end)
        end -- end match
    end
), 
show goal, from begin
    cases a : ha,
    exact base a,
    exact it a,
end -/

theorem while_right (c : σ₂ → bool) (k) (V : ∀ {n₂} (s₂ : state n₂ σ₂ τ₂) (ac₂ : vector bool n₂), ℕ)
(h₁ : ∀ {n₁ s₁ ac₁ n₂ s₂ ac₂}, I n₁ s₁ ac₁ n₂ s₂ ac₂ → I n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂)) 
(h₂ : ∀ {n₁ s₁ ac₁ n₂ s₂ ac₂} {s : state n₂ σ₂ τ₂}, I n₁ s₁ ac₁ n₂ s₂ (deactivate_threads (bnot ∘ c) ac₂ s) → I n₁ s₁ ac₁ n₂ s₂ ac₂)
(hb : ∀ n, {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, I n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₂.active_threads ac₂).all (λts, c ts.tlocal) ∧ V s₂ ac₂ = n *} kernel.compute id ~> k {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, I n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ V s₂ (deactivate_threads (bnot ∘ c) ac₂ s₂) < n *}) :
{* I *} kernel.compute id ~> kernel.loop c k {* I *} := sorry

theorem while_left (c : σ₁ → bool) (k) (V : ∀ {n₂} (s₂ : state n₂ σ₂ τ₂) (ac₂ : vector bool n₂), ℕ)
(h₁ : ∀ {n₁ s₁ ac₁ n₂ s₂ ac₂}, I n₁ s₁ ac₁ n₂ s₂ ac₂ → I n₁ s₁ (deactivate_threads (bnot ∘ c) ac₁ s₁) n₂ s₂ ac₂) 
(h₂ : ∀ {n₁ s₁ ac₁ n₂ s₂ ac₂} {s : state n₁ σ₁ τ₁}, I n₁ s₁ (deactivate_threads (bnot ∘ c) ac₁ s) n₂ s₂ ac₂ → I n₁ s₁ ac₁ n₂ s₂ ac₂)
(hb : {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, I n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₁.active_threads ac₁).all (λts, c ts.tlocal) *} k ~> kernel.compute id {* λ n₁ s₁ ac₁ n₂ s₂ ac₂, I n₁ s₁ ac₁ n₂ s₂ ac₂ *}) :
{* I *} kernel.loop c k ~> kernel.compute id {* I *} := begin
    apply swap,
    {
        sorry, -- we need the assumption that the loop terminates here
    },
    sorry,
end

theorem ite_left' (c : σ₁ → bool) (th) (el)
(h₁ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → P n₁ s₁ (deactivate_threads (bnot ∘ c) ac₁ s₁) n₂ s₂ ac₂) 
(h₂ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₁ σ₁ τ₁), Q n₁ s₁ (deactivate_threads (bnot ∘ c) ac₁ s') n₂ s₂ ac₂ → Q n₁ s₁ ac₁ n₂ s₂ ac₂)
(h₃ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₁ σ₁ τ₁), Q n₁ s₁ ac₁ n₂ s₂ ac₂ → Q n₁ s₁ (deactivate_threads c ac₁ s') n₂ s₂ ac₂)
(h₄ : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂ (s' : state n₁ σ₁ τ₁), R n₁ s₁ (deactivate_threads c ac₁ s') n₂ s₂ ac₂ → R n₁ s₁ ac₁ n₂ s₂ ac₂) :
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₁.active_threads ac₁).all (λts, c ts.tlocal) *} th ~> kernel.compute id {* Q *} →
{* λ n₁ s₁ ac₁ n₂ s₂ ac₂, Q n₁ s₁ ac₁ n₂ s₂ ac₂ ∧ (s₁.active_threads ac₁).all (λts, bnot $ c ts.tlocal) *} el ~> kernel.compute id {* R *} →
{* P *} kernel.ite c th el ~> kernel.compute id {* R *} := begin
    intros hth hel,
    apply swap',
    {
        apply ite_right',
        swap 5, {
            apply swap,
            apply consequence,
            apply hth,
            {
                intros,
                exact ⟨a.left.left, a.right⟩,
            }, {
                intros,
                exact a,
            },
            intros,
            cases a.left.right,
            cases h,
            
            sorry, -- we need proof that th terminates
        }, 
        swap 5, {
            apply swap,
            apply hel,
            sorry, -- we need proof that el terminates
        }, {
            intros,
            split,
            apply h₁,
            exact a.left,
            sorry,
        }, {
            intros,
            apply h₂,
            exact a,
        }, {
            intros,
            apply h₃,
            exact a,
        }, {
            sorry,
        }
    }, {
        intros,
        use s₁,
        apply exec_skip,
    }
end

lemma kernel_foldr_skip_right {k : kernel σ₂ τ₂} {ks} : 
{* P *} k₁ ~> list.foldr kernel.seq k ks {* Q *} ↔ {* P *} k₁ ~> list.foldr kernel.seq (kernel.compute id) ks ;; k {* Q *} := sorry

end parlang