import parlang
import parlang_nonmono

namespace parlang
namespace ac_loop

open parlang
open parlang.kernel
open parlang_nonmono

variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} {s t u : state n σ τ} {ac : vector bool n} {f f' : σ → bool}  [decidable_eq ι] {semantics : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop}

class has_unique (semantics : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop) := 
(unique : ∀ {k : kernel σ τ} {ac : vector bool n} {s t t' : state n σ τ}, semantics k ac s t → semantics k ac s t' → t = t')

variables [has_unique semantics]

instance unique2 : has_unique $ @parlang.exec_state σ ι τ _ n := ⟨begin
    intros _ _ _ _ _ a b,
    apply parlang.exec_state_unique b a,
end⟩

instance unique1 : has_unique $ @exec_state σ ι τ _ n := sorry

notation `v[` v:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := v

-- this is similar to the semantic itself except we are not interested in states but the resulting active maps
inductive ac_after_n_iteration (semantics : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop) (k : kernel σ τ) (f : σ → bool) : state n σ τ → vector bool n → vector bool n → ℕ → Prop
| base (ac : vector bool n) (s : state n σ τ) : ac_after_n_iteration s ac ac 0
| step {ac : vector bool n} (s t : state n σ τ) {i : ℕ} {ac' : vector bool n} : ac_after_n_iteration t (deactivate_threads (bnot ∘ f) ac s) ac' i → semantics k (deactivate_threads (bnot ∘ f) ac s) s t → ac_after_n_iteration s ac ac' (i + 1)

example : ac_after_n_iteration exec_state (compute (λ (m : bool), ff)) id (@parlang.init_state bool string (λs, ℕ) _ (λ_, tt) (λ_,1) (λs:string, 0)) v[tt] v[tt] 1 := begin
    apply ac_after_n_iteration.step _ (@parlang.init_state bool string (λs, ℕ) _ (λ_, ff) (λ_,1) (λs:string, 0)),
    swap,
    sorry,
    sorry,
end

lemma ac_after_n_iteration_unique {k : kernel σ τ} {f : σ → bool} {ac' ac'' : vector bool n} {i} : 
ac_after_n_iteration semantics k f s ac ac' i → ac_after_n_iteration semantics k f s ac ac'' i → ac' = ac'' := begin
    admit,
end

lemma ac_ge_single {k : kernel σ τ} {f : σ → bool} {ac' : vector bool n} {i : ℕ} : ac_after_n_iteration semantics k f s ac ac' i → ac ≥ ac' := begin
    intros h,
    induction i generalizing s ac ac',
    case nat.zero {
        cases h,
        intros t hna,
        assumption,
    },
    case nat.succ {
        cases h,
        specialize i_ih h_a,
        have : ac ≥ (deactivate_threads (bnot ∘ f) ac s) := by apply ac_sub_deac,
        sorry, -- proof by transitivity
    }
end

lemma ac_ge_two {k : kernel σ τ} {f : σ → bool} {i i' : ℕ} {ac' ac'' : vector bool n} : 
ac_after_n_iteration semantics k f s ac ac' i → ac_after_n_iteration semantics k f s ac ac'' (i + i') → ac' ≥ ac'' := begin
    intros h₁ h₂,
    induction i generalizing s ac,
    case nat.zero {
        cases h₁,
        apply ac_ge_single h₂,
    },
    case nat.succ {
        cases h₁,
        have : nat.succ i_n + i' = nat.succ (i_n + i') := by rw nat.succ_add,
        rw this at h₂,
        cases h₂,
        have : h₁_t = h₂_t := has_unique.unique _ _ _ h₁_a_1 h₂_a_1,
        subst this,
        apply i_ih h₁_a h₂_a,
    }
end

def monotone_loop (semantics : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop) (f k) (s : state n σ τ) (ac : vector bool n) : Prop := 
∀ (i i' : ℕ) (ac' ac'' : vector bool n), ac_after_n_iteration semantics k f s ac ac' i → ac_after_n_iteration semantics k f s ac ac'' (i + i') → ac' ≥ ac''

lemma par_loop_ac' {k : kernel σ τ} : parlang.exec_state (loop f k) ac s t → ∃ i ac', ac_after_n_iteration parlang.exec_state k f s ac ac' i ∧ no_thread_active (deactivate_threads (bnot ∘ f) ac' t) := begin
    generalize eq_l : (loop f k) = l,
    intro h,
    induction h;
        cases eq_l,
    {
        use 0,
        use h_ac,
        split,
        apply ac_after_n_iteration.base,
        assumption,
    }, {
        clear h_ih_a,
        specialize h_ih_a_1 rfl,
        cases h_ih_a_1 with i ih,
        cases ih with ac' ih,
        cases ih with ha hb,
        use i + 1,
        use ac',
        split,
        swap,
        assumption,
        apply ac_after_n_iteration.step,
        repeat { assumption },
    }
end

lemma loop_ac' {k : kernel σ τ} : exec_state (loop f k) ac s t → ∃ i ac', ac_after_n_iteration exec_state k f s ac ac' i ∧ no_thread_active (deactivate_threads (bnot ∘ f) ac' t) := begin
    generalize eq_l : (loop f k) = l,
    intro h,
    induction h generalizing;
        cases eq_l,
    {
        use 0,
        use h_ac,
        split,
        apply ac_after_n_iteration.base,
        assumption,
    }, {
        clear h_ih_a,
        specialize h_ih_a_1 rfl,
        cases h_ih_a_1 with i ih,
        cases ih with ac' ih,
        cases ih with ha hb,
        use i + 1,
        use ac',
        split,
        swap,
        assumption,
        {
            apply ac_after_n_iteration.step,
            swap,
            exact h_a_1,
            induction ha,
            case ac_after_n_iteration.base {
                have : monotone_loop exec_state f k h_s ha_ac := by apply ac_ge_two,
                have : monotone_loop exec_state f k h_s ha_ac := by apply ac_ge_two,
            }
        }
    }
end

end ac_loop
end parlang