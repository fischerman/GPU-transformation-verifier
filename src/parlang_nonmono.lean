import parlang

namespace parlang_nonmono
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

open parlang
open parlang.kernel

inductive exec_state {n : ℕ} : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop
| load (f) (s : state n σ τ) (ac : vector bool n) :
  exec_state (load f) ac s (s.map_active_threads ac $ thread_state.load f)
| store (f) (s : state n σ τ) (ac : vector bool n) :
  exec_state (store f) ac s (s.map_active_threads ac $ thread_state.store f)
| compute (f : σ → σ) (s : state n σ τ) (ac : vector bool n) :
  exec_state (compute f) ac s (s.map_active_threads ac $ thread_state.map f)
| sync_all (s : state n σ τ) (ac : vector bool n) (m : memory τ) (hs : s.syncable m)
  (ha : all_threads_active ac) :
  exec_state sync ac s (s.map_threads $ thread_state.sync m)
| sync_none (s : state n σ τ) (ac : vector bool n) (h : no_thread_active ac) :
  exec_state sync ac s s
| seq (s t u : state n σ τ) (ac : vector bool n) (k₁ k₂ : kernel σ τ) :
  exec_state k₁ ac s t → exec_state k₂ ac t u → exec_state (seq k₁ k₂) ac s u
| ite (s t u : state n σ τ) (ac : vector bool n) (f : σ → bool) (k₁ k₂ : kernel σ τ) :
  exec_state k₁ (deactivate_threads (bnot ∘ f) ac s) s t →
  exec_state k₂ (deactivate_threads f ac s) t u →
  exec_state (ite f k₁ k₂) ac s u
  -- in the then-branch we deactive those threads where the condition is false and vice versa
| loop_stop (s : state n σ τ) (ac : vector bool n) (f : σ → bool) (k : kernel σ τ) :
  no_thread_active (deactivate_threads (bnot ∘ f) ac s) →
  exec_state (loop f k) ac s s
| loop_step (s t u : state n σ τ) (ac : vector bool n) (f : σ → bool) (k : kernel σ τ) :
  any_thread_active (deactivate_threads (bnot ∘ f) ac s) →
  exec_state k (deactivate_threads (bnot ∘ f) ac s) s t →
  exec_state (loop f k) ac t u →
  exec_state (loop f k) ac s u


def contains_sync : kernel σ τ → Prop
| sync := true
| (seq a b) := (contains_sync a) ∨ (contains_sync b)
| (ite _ a b) := (contains_sync a) ∨ (contains_sync b)
| (loop _ a) := (contains_sync a)
| _ := false

instance decidable (k : kernel σ τ) : decidable (contains_sync k) := sorry

variables {s t : state n σ τ} {ac : vector bool n}

-- probably has to be an inducive type
-- def ac_after_n_iteration (k : kernel σ τ) (f : σ → bool) : ℕ → state n σ τ → vector bool n → vector bool n
-- | 0 s ac := ac
-- | (n + 1) s ac := if (∃ t, exec_state k ac s t) then ac_after_n_iteration n t (deactivate_threads (bnot ∘ f) ac s) else ac -- all false

-- this is similar to the semantic itself except we are not interested in states but the resulting active maps
-- it is reversed, maybe we should build it the other way around
inductive ac_after_n_iteration (semantics : Π {σ ι : Type} {τ : ι → Type} [_inst_1 : decidable_eq ι] {n : ℕ}, kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop) (k : kernel σ τ) (f : σ → bool) : state n σ τ → vector bool n → vector bool n → ℕ → Prop
| base (ac : vector bool n) (s : state n σ τ) : ac_after_n_iteration s ac ac 0
| step (ac : vector bool n) (s t : state n σ τ) (i : ℕ) (ac' : vector bool n) : ac_after_n_iteration t (deactivate_threads (bnot ∘ f) ac t) ac' i → semantics k ac s t → ac_after_n_iteration s ac ac' (i + 1)
--| step (ac : vector bool n) (s t : state n σ τ) (i : ℕ) (ac' : vector bool n) : ac_after_n_iteration s ac ac' i → exec_state k ac' s t → ac_after_n_iteration s ac (deactivate_threads (bnot ∘ f) ac t) (i + 1)

lemma ac_after_n_iteration_unique {k : kernel σ τ} {f : σ → bool} {ac' ac'' : vector bool n} {i} : 
ac_after_n_iteration @parlang.exec_state k f s ac ac' i → ac_after_n_iteration @parlang.exec_state k f s ac ac'' i → ac' = ac'' := begin
    admit,
end

def ac_ge (ac' : vector bool n) (ac : vector bool n) : Prop := ∀ (t : fin n), ¬ (ac.nth t) → ¬ (ac'.nth t)

instance : has_le (vector bool n) := ⟨ac_ge⟩

lemma ac_sub_deac {f : σ → bool} : ac ≥ (deactivate_threads (bnot ∘ f) ac s) := begin
    intros t h₁ h₂,
    apply h₁,
    unfold deactivate_threads at h₂,
    rw vector.nth_map at h₂,
    rw vector.nth_map₂ at h₂,
    rw deactivate_threads._match_1 at h₂,
    rw band_coe_iff at h₂,
    cases h₂,
    assumption,
end

lemma ac_ge_single {k : kernel σ τ} {f : σ → bool} {ac' : vector bool n} {i : ℕ} : ac_after_n_iteration @parlang.exec_state k f s ac ac' i → ac ≥ ac' := begin
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

example {ac' ac'' : vector bool n} {k : kernel σ τ} {f : σ → bool} {i : ℕ} : 
ac_after_n_iteration @parlang.exec_state k f s ac ac' i → ac_after_n_iteration @parlang.exec_state k f s ac ac'' (i + 1) → ac' ≥ ac'' := begin
    intros h₁ h₂,
    induction i generalizing s ac,
    case nat.zero {
        cases h₁,
        cases h₂,
        cases h₂_a,
        apply ac_sub_deac,
    },
    case nat.succ {
        cases h₁,
        cases h₂,
        have : h₁_t = h₂_t := exec_state_unique h₂_a_1 h₁_a_1,
        subst this,
        apply i_ih h₁_a h₂_a,
    }
end

lemma ac_ge_two {k : kernel σ τ} {f : σ → bool} {i i' : ℕ} {ac' ac'' : vector bool n} : 
ac_after_n_iteration @parlang.exec_state k f s ac ac' i → ac_after_n_iteration @parlang.exec_state k f s ac ac'' (i + i') → ac' ≥ ac'' := begin
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
        have : h₁_t = h₂_t := exec_state_unique h₂_a_1 h₁_a_1,
        subst this,
        apply i_ih h₁_a h₂_a,
    }
end

def monotone_loop (f k) (s : state n σ τ) (ac : vector bool n) : Prop := 
∀ (i i' : ℕ) (ac' ac'' : vector bool n), ac_after_n_iteration @parlang.exec_state k f s ac ac' i → ac_after_n_iteration @parlang.exec_state k f s ac ac'' (i + i') → ac' ≥ ac''

example (k : kernel σ τ) (ac : vector bool n) (s s' : state n σ τ) : exec_state k ac s s' ↔ parlang.exec_state k ac s s' := begin
    split,
    {
        intro h,
        induction h,
        {
            apply parlang.exec_state.load,
        }, {
            apply parlang.exec_state.store,
        }, {
            apply parlang.exec_state.compute,
        }, {
            apply parlang.exec_state.sync_all,
            repeat { assumption },
        }, {
            apply parlang.exec_state.sync_none,
            assumption,
        }, {
            apply parlang.exec_state.seq,
            repeat { assumption },
        }, {
            apply parlang.exec_state.ite,
            repeat { assumption },
        }, {
            apply parlang.exec_state.loop_stop,
            assumption,
        }, {
            apply parlang.exec_state.loop_step,
            repeat { assumption },
            have : monotone_loop h_f h_k h_s h_ac := by apply ac_ge_two,
            
        },
    }, {
        intro h,
        induction h,
        {
            apply exec_state.load,
        }, {
            apply exec_state.store,
        }, {
            apply exec_state.compute,
        }, {
            apply exec_state.sync_all,
            repeat { assumption },
        }, {
            apply exec_state.sync_none,
            assumption,
        }, {
            apply exec_state.seq,
            repeat { assumption },
        }, {
            apply exec_state.ite,
            repeat { assumption },
        }, {
            apply exec_state.loop_stop,
            assumption,
        }, {
            apply exec_state.loop_step,
            repeat { assumption },
        },
    }
end

end parlang_nonmono