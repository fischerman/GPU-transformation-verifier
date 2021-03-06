import parlang.defs
import parlang.lemmas_state
import parlang.lemmas_exec

namespace parlang_nonmono
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]
notation `v[` v:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := v

open parlang
open parlang.kernel

inductive exec_state {n : ℕ} : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop
| load (f) (s : state n σ τ) (ac : vector bool n) :
  exec_state (load f) ac s (s.map_active_threads ac $ thread_state.load f)
| store (f) (s : state n σ τ) (ac : vector bool n) :
  exec_state (store f) ac s (s.map_active_threads ac $ thread_state.store f)
| compute (f : σ → σ) (s : state n σ τ) (ac : vector bool n) :
  exec_state (compute f) ac s (s.map_active_threads ac $ thread_state.compute f)
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
| loop_stop (s : state n σ τ) (ac : vector bool n) (f : σ → bool) (k : kernel σ τ) :
  no_thread_active (deactivate_threads (bnot ∘ f) ac s) →
  exec_state (loop f k) ac s s
| loop_step (s t u : state n σ τ) (ac : vector bool n) (f : σ → bool) (k : kernel σ τ) :
  any_thread_active (deactivate_threads (bnot ∘ f) ac s) →
  exec_state k (deactivate_threads (bnot ∘ f) ac s) s t →
-- the only difference to parlang is the line below; here we don't deactivate threads
  exec_state (loop f k) ac t u →
  exec_state (loop f k) ac s u

variables {s t u : state n σ τ} {ac : vector bool n} {f f' : σ → bool} 

/-- This proof is for nonmono. Parlang proof is similar -/
lemma exec_state_inactive_threads_untouched {s u : state n σ τ} {ac : vector bool n} {k} : exec_state k ac s u → ∀ i, ¬ ac.nth i → s.threads.nth i = u.threads.nth i := begin
    intros he i hna,
    induction he,
    case exec_state.load {
        apply state.map_active_threads_nth_inac hna,
    },
    case exec_state.store {
        apply state.map_active_threads_nth_inac hna,
    },
    case exec_state.compute {
        apply state.map_active_threads_nth_inac hna,
    },
    case exec_state.sync_all {
        have : ↥(vector.nth he_ac i) := by apply all_threads_active_nth he_ha,
        contradiction,
    },
    case exec_state.sync_none {
        refl,
    },
    case exec_state.seq {
        rw he_ih_a hna,
        rw he_ih_a_1 hna,
    },
    case exec_state.ite {
        rw he_ih_a (deactivate_threads_deactivate_inactive_thread hna),
        rw ← he_ih_a_1 (deactivate_threads_deactivate_inactive_thread hna),
    },
    case exec_state.loop_stop {
        refl,
    },
    case exec_state.loop_step {
        rw he_ih_a (deactivate_threads_deactivate_inactive_thread hna),
        rw ← he_ih_a_1 hna,
    }
end

lemma monotonic_exec {f k} : 
exec_state k (deactivate_threads (bnot ∘ f) ac s) s t →
deactivate_threads (bnot ∘ f) ac s ≥ deactivate_threads (bnot ∘ f) ac t := begin
    intro h,
    intros tid,
    unfold deactivate_threads,
    repeat { rw vector.nth_map },
    repeat { rw vector.nth_map₂ },
    repeat { rw deactivate_threads._match_1 },
    repeat { rw band_coe_iff },
    intros hna ha,
    cases ha,
    apply hna,
    clear hna,
    split, 
    {
        simp only [bool.bnot_bnot] at ha_left,
        simp only [bool.bnot_bnot],
        by_cases e : f ((vector.nth (s.threads) tid).tlocal) = tt,
        { assumption, },
        rw exec_state_inactive_threads_untouched h tid,
        assumption,
        simp at e,
        simp [deactivate_threads, *],
    }, {
        assumption,
    }
end

lemma parlang_monotonic_exec {f k} : 
parlang.exec_state k (deactivate_threads (bnot ∘ f) ac s) s t →
deactivate_threads (bnot ∘ f) ac s ≥ deactivate_threads (bnot ∘ f) ac t := begin
    intro h,
    intros tid,
    unfold deactivate_threads,
    repeat { rw vector.nth_map },
    repeat { rw vector.nth_map₂ },
    repeat { rw deactivate_threads._match_1 },
    repeat { rw band_coe_iff },
    intros hna ha,
    cases ha,
    apply hna,
    clear hna,
    split, 
    {
        simp only [bool.bnot_bnot] at ha_left,
        simp only [bool.bnot_bnot],
        by_cases e : f ((vector.nth (s.threads) tid).tlocal) = tt,
        { assumption, },
        rw parlang.exec_state_inactive_threads_untouched h tid,
        assumption,
        simp at e,
        simp [deactivate_threads, *],
    }, {
        assumption,
    }
end

-- the goal eventually has to deacs, only the most pessimistic stays
lemma exec_ac_to_deac.aux {k} (ha : any_thread_active (deactivate_threads (bnot ∘ f) ac s)) (hi : parlang.exec_state k (deactivate_threads (bnot ∘ f) ac s) s t) (h : parlang.exec_state (loop f k) ac t u) :
parlang.exec_state (loop f k) (deactivate_threads (bnot ∘ f) ac s) t u := begin
    have hgest : deactivate_threads (bnot ∘ f) ac s ≥ deactivate_threads (bnot ∘ f) ac t := parlang_monotonic_exec hi,
    generalize_hyp eq_l : (loop f k) = l at h ⊢,
    clear hi,
    induction h;
        cases eq_l,
    {
        apply parlang.exec_state.loop_stop,
        rw ac_deac_ge hgest,
        exact h_a,
    }, {
        clear t u,
        rename h_s t,
        rename h_t t₂,
        rename h_u u,
        rename h_ih_a_1 ih,
        rename h_a_1 htt₂,
        clear h_ih_a,
        have hgett₂ : deactivate_threads (bnot ∘ f) h_ac t ≥ deactivate_threads (bnot ∘ f) h_ac t₂ := parlang_monotonic_exec htt₂,
        have hgest₂ : deactivate_threads (bnot ∘ f) h_ac s ≥ deactivate_threads (bnot ∘ f) h_ac t₂ := ac_trans hgest hgett₂,
        apply parlang.exec_state.loop_step,
        {
            rw ac_deac_ge hgest,
            assumption,
        }, {
            rw ac_deac_ge hgest,
            assumption,
        }, {
            rw ac_deac_comm,
            apply ih,
            {
                rw ac_deac_comm,
                rw ac_deac_ge hgest,
                assumption,
            }, {
                rw ac_deac_comm,
                rw ac_deac_ge hgest,
                rw ac_deac_ge hgett₂,
                exact hgett₂,
            },
            refl,
        }
    }
end

lemma exec_ac_to_deac {k} (ha : any_thread_active (deactivate_threads (bnot ∘ f) ac s)) (hi : parlang.exec_state k (deactivate_threads (bnot ∘ f) ac s) s t) (h : parlang.exec_state (loop f k) ac t u) :
parlang.exec_state (loop f k) ac s u := begin
    have := exec_ac_to_deac.aux ha hi h,
    apply parlang.exec_state.loop_step,
    repeat { assumption },
end

-- deactivations stack up in the assumption, only the most recent one matters
lemma exec_deac_to_ac.aux {k} (ha : any_thread_active (deactivate_threads (bnot ∘ f) ac s)) (hi : exec_state k (deactivate_threads (bnot ∘ f) ac s) s t) (h : exec_state (loop f k) (deactivate_threads (bnot ∘ f) ac s) t u) :
exec_state (loop f k) ac t u := begin
    have hgest : deactivate_threads (bnot ∘ f) ac s ≥ deactivate_threads (bnot ∘ f) ac t := monotonic_exec hi,
    generalize_hyp eq_ac : (deactivate_threads (bnot ∘ f) ac s) = dac at h hi, -- we need this, otherwise we have two disjoint ac
    generalize_hyp eq_l : (loop f k) = l at h ⊢,
    clear hi,
    induction h;
        cases eq_l;
    subst eq_ac,
    {
        apply exec_state.loop_stop,
        rw ac_deac_ge hgest at h_a,
        exact h_a,
    }, {
        clear t u,
        rename h_s t,
        rename h_t t₂,
        rename h_u u,
        rename h_ih_a_1 ih,
        rename h_a_1 htt₂,
        clear h_ih_a,
        rw ac_deac_ge hgest at htt₂,
        have hgett₂ : deactivate_threads (bnot ∘ f) ac t ≥ deactivate_threads (bnot ∘ f) ac t₂ := monotonic_exec htt₂,
        have hgest₂ : deactivate_threads (bnot ∘ f) ac s ≥ deactivate_threads (bnot ∘ f) ac t₂ := ac_trans hgest hgett₂,
        specialize ih hgest₂ rfl rfl,
        apply exec_state.loop_step,
        swap 3,
        apply ih,
        rw ac_deac_ge hgest at h_a,
        exact h_a,
        exact htt₂,
    }
end

lemma exec_deac_to_ac {k} (ha : any_thread_active (deactivate_threads (bnot ∘ f) ac s)) (hi : exec_state k (deactivate_threads (bnot ∘ f) ac s) s t) (h : exec_state (loop f k) (deactivate_threads (bnot ∘ f) ac s) t u) :
exec_state (loop f k) ac s u := begin
    have := exec_deac_to_ac.aux ha hi h,
    apply exec_state.loop_step,
    repeat { assumption },
end

lemma eq_parlang_parlangnonmono (k : kernel σ τ) (ac : vector bool n) (s s' : state n σ τ) : exec_state k ac s s' ↔ parlang.exec_state k ac s s' := begin
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
            apply exec_ac_to_deac,
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
        }, 
        case parlang.exec_state.loop_step : a b c ac f k' ha hel hek ih₁ ih₂ {
            apply exec_deac_to_ac,
            repeat { assumption },
        },
    }
end

end parlang_nonmono