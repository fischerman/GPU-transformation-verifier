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
inductive ac_after_n_iteration (k : kernel σ τ) (f : σ → bool) : state n σ τ → vector bool n → vector bool n → ℕ → Prop
| base (ac : vector bool n) (s : state n σ τ) : ac_after_n_iteration s ac ac 0
| iteration (ac : vector bool n) (s t : state n σ τ) (i : ℕ) (ac' : vector bool n) : ac_after_n_iteration s ac ac' i → exec_state k ac' s t → ac_after_n_iteration s ac (deactivate_threads (bnot ∘ f) ac' t) (i + 1)
| done (i : ℕ) (ac : vector bool n) (s t : state n σ τ) : ¬exec_state k ac s t → ac_after_n_iteration s ac ac i

lemma ac_after_n_iteration_unique {k : kernel σ τ} {f : σ → bool} {ac' ac'' : vector bool n} {i} : 
ac_after_n_iteration k f s ac ac' i → ac_after_n_iteration k f s ac ac'' i → ac' = ac'' := begin
    admit,
end

def monotone_loop (f k) (s : state n σ τ) (ac : vector bool n) : Prop := 
∀ (i i' : ℕ) (ac' ac'' : vector bool n), ac_after_n_iteration k f s ac ac' i ∧ ac_after_n_iteration k f s ac ac'' (i + i') →
(∀ (t : fin n), ¬ (ac'.nth t) → ¬ (ac''.nth t))

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
            have : monotone_loop h_f h_k h_s h_ac := begin
                intros i i' ac' ac'' hit t hin,
                cases hit,
                induction i',
                case nat.zero {
                    have : ac' = ac'' := ac_after_n_iteration_unique hit_left hit_right,
                    subst this,
                    exact hin,
                },
                case nat.succ {
                    apply i'_ih,
                    cases hit_right,
                    case parlang_nonmono.ac_after_n_iteration.iteration {
                        --apply hit_right_a,
                        admit,
                    },
                    case parlang_nonmono.ac_after_n_iteration.done {
                        cases hit_left,
                        case parlang_nonmono.ac_after_n_iteration.done {
                            admit, -- can be done
                        },
                        case parlang_nonmono.ac_after_n_iteration.base {
                            
                        }
                    },
                }
            end,
            
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