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