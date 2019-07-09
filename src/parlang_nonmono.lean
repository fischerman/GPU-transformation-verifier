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

variables {s t u : state n σ τ} {ac : vector bool n} {f f' : σ → bool} {semantics : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop}

class has_unique (semantics : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop) := 
(unique : ∀ {k : kernel σ τ} {ac : vector bool n} {s t t' : state n σ τ}, semantics k ac s t → semantics k ac s t' → t = t')

variables [has_unique semantics]

instance unique2 : has_unique $ @parlang.exec_state σ ι τ _ n := ⟨begin
    intros _ _ _ _ _ a b,
    apply parlang.exec_state_unique b a,
end⟩

instance unique1 : has_unique $ @exec_state σ ι τ _ n := sorry

def ac_ge (ac' : vector bool n) (ac : vector bool n) : Prop := ∀ (t : fin n), ¬ (ac.nth t) → ¬ (ac'.nth t)

instance : has_le (vector bool n) := ⟨ac_ge⟩

lemma exec_state_inactive_threads_untouched {s u : state n σ τ} {ac : vector bool n} {k} : exec_state k ac s u → ∀ i, ¬ ac.nth i → s.threads.nth i = u.threads.nth i := begin
    admit,
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
        simp [deactivate_threads, *],
        sorry, -- trivial
    }, {
        assumption,
    }
end

-- probably has to be an inducive type
-- def ac_after_n_iteration (k : kernel σ τ) (f : σ → bool) : ℕ → state n σ τ → vector bool n → vector bool n
-- | 0 s ac := ac
-- | (n + 1) s ac := if (∃ t, exec_state k ac s t) then ac_after_n_iteration n t (deactivate_threads (bnot ∘ f) ac s) else ac -- all false

-- this is similar to the semantic itself except we are not interested in states but the resulting active maps
-- it is reversed, maybe we should build it the other way around
inductive ac_after_n_iteration (semantics : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop) (k : kernel σ τ) (f : σ → bool) : state n σ τ → vector bool n → vector bool n → ℕ → Prop
| base (ac : vector bool n) (s : state n σ τ) : ac_after_n_iteration s ac ac 0
| step {ac : vector bool n} (s t : state n σ τ) {i : ℕ} {ac' : vector bool n} : ac_after_n_iteration t (deactivate_threads (bnot ∘ f) ac s) ac' i → semantics k (deactivate_threads (bnot ∘ f) ac s) s t → ac_after_n_iteration s ac ac' (i + 1)
--| step (ac : vector bool n) (s t : state n σ τ) (i : ℕ) (ac' : vector bool n) : ac_after_n_iteration s ac ac' i → exec_state k ac' s t → ac_after_n_iteration s ac (deactivate_threads (bnot ∘ f) ac t) (i + 1)

-- this semantic would require that in and out ac are always the same
inductive ac_after_n_iteration_nonmono (semantics : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop) (k : kernel σ τ) (f : σ → bool) : state n σ τ → vector bool n → vector bool n → ℕ → Prop
| base (ac : vector bool n) (s : state n σ τ) : ac_after_n_iteration_nonmono s ac ac 0
| step {ac : vector bool n} (s t : state n σ τ) {i : ℕ} {ac' : vector bool n} : ac_after_n_iteration_nonmono t ac ac' i → semantics k (deactivate_threads (bnot ∘ f) ac s) s t → ac_after_n_iteration_nonmono s ac ac' (i + 1)

example {k f} {ac' : vector bool n} {i} : ac_after_n_iteration semantics k f s ac ac' i ↔ ac_after_n_iteration_nonmono semantics k f s ac ac' i := begin
    split, {
        revert ac ac' s,
        induction i,
        case nat.zero {
            intros ac ac' s h,
            cases h,
            apply ac_after_n_iteration_nonmono.base,
        },
        case nat.succ {
            intros ac ac' s h,
            cases h,
            rename h_t t,
            apply ac_after_n_iteration_nonmono.step,
            swap,
            exact h_a_1,
            apply i_ih,
            clear i_ih,
            cases i_n,
            case nat.zero {

            }
            
        }
    }
end

notation `v[` v:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := v

example : ac_after_n_iteration exec_state (compute (λ (m : bool), ff)) id (@parlang.init_state bool string (λs, ℕ) _ (λ_, tt) (λ_,1) (λs:string, 0)) v[tt] v[tt] 1 := begin
    apply ac_after_n_iteration.step _ (@parlang.init_state bool string (λs, ℕ) _ (λ_, ff) (λ_,1) (λs:string, 0)),
    swap,
    sorry,
    apply ac_after_n_iteration.base,
end

lemma ac_after_n_iteration_unique {k : kernel σ τ} {f : σ → bool} {ac' ac'' : vector bool n} {i} : 
ac_after_n_iteration semantics k f s ac ac' i → ac_after_n_iteration semantics k f s ac ac'' i → ac' = ac'' := begin
    admit,
end

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

lemma ac_deac_comm : deactivate_threads f (deactivate_threads f' ac s) t = deactivate_threads f' (deactivate_threads f ac t) s := begin
    induction n,
    case nat.zero {
        apply vector.vector_0_eq',
    },
    case nat.succ {
        sorry,
    }
end

lemma ac_trans {ac' ac'' : vector bool n} : ac ≥ ac' → ac' ≥ ac'' → ac ≥ ac'' := begin
    admit,
end

lemma ac_deac_ge (h : deactivate_threads f ac s ≥ deactivate_threads f' ac t) : deactivate_threads f' (deactivate_threads f ac s) t = deactivate_threads f' ac t := begin
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

#print parlang_nonmono.exec_state.rec_on

lemma loop_ac {k : kernel σ τ}  (h : exec_state (loop f k) ac s t) : ∃ i ac', ac_after_n_iteration exec_state k f s ac ac' i ∧ no_thread_active (deactivate_threads (bnot ∘ f) ac' t)
:= h.rec_on 
    (λ f s ac, _)
    _
    _
    _
    _
    _
    _
    _
    (λ s t u ac f k h₁ h₂ h₃ ih₁ (ih₂ : ∃ (i : ℕ) (ac' : vector bool n), ac_after_n_iteration exec_state k f s ac ac' i ∧ ↥(no_thread_active (deactivate_threads (bnot ∘ f) ac' t))), (show ∃ i ac', ac_after_n_iteration exec_state k f s ac ac' i ∧ no_thread_active (deactivate_threads (bnot ∘ f) ac' t), by begin 

    end))

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

lemma loop_ac' {k : kernel σ τ} : exec_state (loop f k) ac s t ↔ ∃ i ac', ac_after_n_iteration exec_state k f s ac ac' i ∧ no_thread_active (deactivate_threads (bnot ∘ f) ac' t) := begin
    split,
    {
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
                case parlang_nonmono.ac_after_n_iteration.base {
                    have : monotone_loop exec_state f k h_s ha_ac := by apply ac_ge_two,
                    have : monotone_loop exec_state f k h_s ha_ac := by apply ac_ge_two,
                }
            }
        }
    }
end

#print loop_ac'

#print deactivate_threads._match_1

lemma vv {k} (ha : any_thread_active (deactivate_threads (bnot ∘ f) ac s)) (hi : exec_state k (deactivate_threads (bnot ∘ f) ac s) s t) (h : exec_state (loop f k) (deactivate_threads (bnot ∘ f) ac s) t u) :
exec_state (loop f k) ac s u := begin
    apply exec_state.loop_step,
    repeat { assumption },
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
            have : monotone_loop parlang.exec_state h_f h_k h_s h_ac := by apply ac_ge_two,
            admit,
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
            apply vv,
            repeat { assumption },
        },
    }
end

end parlang_nonmono