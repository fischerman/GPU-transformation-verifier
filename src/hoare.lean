import parlang
import aux

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
    -- we reorder the execution (and state transition respectively) to macht the hoare triplets using exec_state_comm_distinct_ac
    -- either the condition holds or not for any thread i
    -- ?? in either case we have to go through both executions ??
    by_cases hc : (c (vector.nth (s.threads) i).tlocal = tt),
    {
        apply h_then,
        -- apply h_then _ he_a,
        -- { apply active_map_deactivate_threads hac hc, },
        -- intros i' hac',
        -- apply and.intro,
        -- {
        --     apply hp i',
        --     apply deactivate_threads_alive hac',
        -- }, {
        --     sorry
        -- }
    }, {
        unfold hoare at h_then h_else,
        apply h_else _,

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