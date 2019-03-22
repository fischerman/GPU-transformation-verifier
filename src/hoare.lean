import parlang
import aux
import data.bool

namespace parlang

variables {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

/-
    because this holds for all n and ac the pre- and postcondition probably contain ite or forall quantifiers
-/
def hoare (P : thread_state σ τ → Prop) (k : kernel σ τ) (Q : thread_state σ τ → Prop) : Prop :=
∀ {n} {s u : state n σ τ} {ac : vector bool n}, (∀i : fin n, ac.nth i → P (s.threads.nth i)) → exec_state k ac s u → (∀i : fin n, ac.nth i → Q (u.threads.nth i))

notation `{* ` P : 1 ` *} ` k : 1 ` {* ` Q : 1 ` *}` := hoare P k Q

example (P Q : thread_state σ τ → Prop) (k₁ k₂ : kernel σ τ) (c : σ → bool) : 
    {* λ (t : thread_state σ τ), P t ∧ c t.tlocal *} k₁ {* Q *} → -- how is it possible that by loosening up the assumptions (i. e. and something to P) the proof gets possible?
    {* λ (t : thread_state σ τ), P t ∧ ¬c t.tlocal *} k₂ {* Q *} → 
    {* P *} kernel.ite c k₁ k₂ {* Q *} := 
begin
    intros h_then h_else n s u ac hp he i hac,
    cases he,
    have : _ := exec_state_comm_distinct_ac _ he_a he_a_1,
    cases this with t' this,
    -- we reorder the execution (and state transition respectively) to macht the hoare triplets using exec_state_comm_distinct_ac
    -- either the condition holds or not for any thread i
    -- ?? in either case we have to go through both executions ??
    by_cases hc : (c (vector.nth (s.threads) i).tlocal = tt),
    {
        apply h_then,
        tactic.swap,
        exact this.right,
        intros i' hh,
        have hh' : _ := deactivate_threads_alive hh,
        have heqst' : vector.nth (s.threads) i' = vector.nth (t'.threads) i' := begin
            apply exec_state_inactive_threads_untouched this.left,
            apply deactivate_threads_complement hh,
        end,
        rw ← heqst',
        apply and.intro,
        {
            exact hp i' hh',
        }, {
            exact deactivate_threads_condition hh,
        }, {
            apply active_map_deactivate_threads hac (bool.eq_tt_coe.mpr hc),
        },
    }, {
        apply h_else,
        tactic.swap,
        exact he_a_1,
        intros i' hh,
        have hh' : _ := deactivate_threads_alive hh,
        have heqst' : vector.nth (s.threads) i' = vector.nth (he_t.threads) i' := begin
            apply exec_state_inactive_threads_untouched he_a,
            apply deactivate_threads_complement,
            rw bool.bnot_bnot,
            exact hh,
        end,
        rw ← heqst',
        apply and.intro,
        {
            exact hp i' hh',
        }, {
            exact deactivate_threads_condition' hh,
        }, {
            rw ← bool.eq_tt_coe at hc,
            apply active_map_deactivate_threads' hac hc,
        }
    }, {

    }
end

example : 
    {* λ (t : thread_state (ℕ × ℕ) τ), t.tlocal.1 = 0 ∧ t.tlocal.1 = 0 *} kernel.compute (λ l, (l.1, 1)) {* λ (t : thread_state (ℕ × ℕ) τ), t.tlocal.2 = 1 *} →
    {* λ (t : thread_state (ℕ × ℕ) τ), t.tlocal.1 = 0 ∧ ¬t.tlocal.1 = 0 *} kernel.compute (λ l, (l.1, 2)) {* λ (t : thread_state (ℕ × ℕ) τ), t.tlocal.2 = 1 *} →
    {* λ (t : thread_state (ℕ × ℕ) τ), t.tlocal.1 = 0 *} kernel.ite (λt, t.1 = 0) (kernel.compute (λ l, (l.1, 1))) (kernel.compute (λ l, (l.1, 2))) {* λ (t : thread_state (ℕ × ℕ) τ), t.tlocal.2 = 1 *} := begin
    intros h_then h_else n s u ac hp he i hac,
    cases he,
end

end parlang