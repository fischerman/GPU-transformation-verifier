import parlang.defs
import parlang.lemmas_active_map
import parlang.lemmas_thread_state
import parlang.lemmas_state

namespace parlang
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

@[simp]
lemma exec_skip {n} {ac : vector bool n} {s} : exec_state (kernel.compute id : kernel σ τ) ac s s := begin
  rw [state.map_active_threads_id s ac] { occs := occurrences.pos [2] },
  apply exec_state.compute,
end

lemma exec_state_unique {s u t : state n σ τ} {ac : vector bool n} {k} (h₁ : exec_state k ac s u) (h₂ : exec_state k ac s t) : t = u := begin
  induction h₁ generalizing t,
  case exec_state.load {
    cases h₂, refl,
  },
  case exec_state.store {
    cases h₂, refl,
  },
  case exec_state.compute {
    cases h₂, refl,
  },
  case exec_state.sync_all {
    cases h₂,
    case parlang.exec_state.sync_all {
      by_cases hl : 0 < n,
      {
        have : h₁_m = h₂_m := by apply state.syncable_unique h₁_hs h₂_hs hl,
        subst this,
        refl,
      },
      {
        have : n = 0 := by simpa using hl,
        subst this,
        simp [state.map_threads],
        rw [vector.vector_0_eq h₁_s.threads, vector.map_nil, vector.map_nil],
      }
    },
    case parlang.exec_state.sync_none {
      by_cases hl : 0 < n,
      exact false.elim (no_threads_active_not_all_threads hl h₂_h h₁_ha),
      have : n = 0 := by simpa using hl,
      subst this,
      rw [state.map_threads, vector.vector_0_eq h₁_s.threads, vector.map_nil],
      sorry,
    },
  },
  case exec_state.sync_none {
    cases h₂,
    case parlang.exec_state.sync_all {
      by_cases hl : 0 < n,
      -- contradiction
      {apply false.elim (no_threads_active_not_all_threads hl h₁_h h₂_ha),},
      {
        by_cases h' : n = 0,
        swap,
        {
          sorry,
        }, {
          subst h',
          cases h₁_s,
          cases h₁_s,
          sorry,
        }
      }
    },
    case parlang.exec_state.sync_none {
      refl,
    }
  },
  case parlang.exec_state.seq {
    cases h₂,
    specialize h₁_ih_a h₂_a,
    subst h₁_ih_a,
    specialize h₁_ih_a_1 h₂_a_1,
    assumption,
  },
  case parlang.exec_state.ite {
    cases h₂,
    specialize h₁_ih_a h₂_a,
    subst h₁_ih_a,
    specialize h₁_ih_a_1 h₂_a_1,
    assumption,
  },
  case parlang.exec_state.loop_stop {
    cases h₂,
    case parlang.exec_state.loop_stop {
      refl,
    },
    case parlang.exec_state.loop_step {
      apply false.elim (no_threads_active_no_active_thread h₁_a h₂_a),
    }
  },
  case parlang.exec_state.loop_step {
    cases h₂,
    case parlang.exec_state.loop_stop {
      apply false.elim (no_threads_active_no_active_thread h₂_a h₁_a),
    },
    case parlang.exec_state.loop_step {
      specialize h₁_ih_a h₂_a_1,
      subst h₁_ih_a,
      specialize h₁_ih_a_1 h₂_a_2,
      assumption,
    }
  }
end

lemma exec_state_precedes {s u : state n σ τ} {ac : vector bool n} {k} : exec_state (k) ac s u → s.precedes u := begin
  intro he,
  cases he,
  case parlang.exec_state.load {
    unfold state.precedes,
    simp,
    intros a b,
    induction n,
    case nat.zero {
      exact match ac with
      | ⟨[], h⟩ := begin
          sorry,
          -- rw vector.map₂_nil',
          -- rw vector.map₂_nil,
          -- intro,
          -- have : (a, b) ∉ (@vector.nil (thread_state σ τ × thread_state σ τ)) := by apply vector.mem_nil,
          -- contradiction,
        end
      end,
    },
    case nat.succ {
      exact match ac, s.threads with
      | ⟨list.cons a ac_tl, h ⟩ := begin
          sorry
        end
      end,
    },
  },
  repeat { admit }
end

lemma exec_state_seq_left {s u : state n σ τ} {ac : vector bool n} {k₁ k₂} : exec_state (k₁ ;; k₂) ac s u → ∃t, exec_state k₁ ac s t ∧ t.precedes u := begin
  intro he,
  cases he,
  apply Exists.intro he_t,
  apply and.intro he_a _,
  apply exec_state_precedes he_a_1,
end

lemma exec_state_inactive_threads_untouched {s u : state n σ τ} {ac : vector bool n} {k} : exec_state k ac s u → ∀ i, ¬ ac.nth i → s.threads.nth i = u.threads.nth i := begin
  intros he i hna,
  induction he,
  case parlang.exec_state.load {
    apply state.map_active_threads_nth_inac hna,
  },
  case parlang.exec_state.store {
    apply state.map_active_threads_nth_inac hna,
  },
  case parlang.exec_state.compute {
    apply state.map_active_threads_nth_inac hna,
  },
  case parlang.exec_state.sync_all {
    have : ↥(vector.nth he_ac i) := by apply all_threads_active_nth he_ha,
    contradiction,
  },
  case parlang.exec_state.sync_none {
    refl,
  },
  case parlang.exec_state.seq {
    rw he_ih_a hna,
    rw he_ih_a_1 hna,
  },
  case parlang.exec_state.ite {
    rw he_ih_a (deactivate_threads_deactivate_inactive_thread hna),
    rw ← he_ih_a_1 (deactivate_threads_deactivate_inactive_thread hna),
  },
  case parlang.exec_state.loop_stop {
    refl,
  },
  case parlang.exec_state.loop_step {
    rw he_ih_a (deactivate_threads_deactivate_inactive_thread hna),
    rw ← he_ih_a_1 (deactivate_threads_deactivate_inactive_thread hna),
  }
end

lemma exec_skip_eq {n} {ac : vector bool n} {s t} : exec_state (kernel.compute id : kernel σ τ) ac s t → t = s := exec_state_unique exec_skip

lemma kernel_transform_inhab {k : kernel σ τ} {n} {ac} {s u} : exec_state k ac s u → ¬contains_sync k → ∃ f, kernel_transform_func k f n ac := begin
  intros h hs,
  unfold kernel_transform_func,
  induction k generalizing s u,
  case parlang.kernel.load {
    apply exists.intro (thread_state.load k),
    intros s u,
    apply iff.intro,
    {
      intro he,
      cases he,
      simp [state.map_active_threads],
    }, {
      intro hm,
      subst hm,
      apply exec_state.load,
    }
  },
  case parlang.kernel.sync {
    apply hs.elim,
    rw contains_sync,
    apply true.intro,
  },
  case parlang.kernel.seq {
    rw contains_sync at hs,
    have h1 : ¬contains_sync k_a := sorry,
    have h2 : ¬contains_sync k_a_1 := sorry,
    cases h,
    specialize k_ih_a h1 h_a,
    specialize k_ih_a_1 h2 h_a_1,
    cases k_ih_a with f,
    cases k_ih_a_1 with g,
    apply exists.intro (g ∘ f),
    intros s' u',
    apply iff.intro,
    {
      intros he,
      cases he,
      have h3 : he_t = state.map_active_threads ac f s' := (k_ih_a_h _ _).mp he_a,
      have h4 : u' = state.map_active_threads ac g he_t := (k_ih_a_1_h _ _).mp he_a_1,
      rw ← state.map_map_active_threads,
      rw h3 at h4,
      exact h4,
    }, {
      intro hmac,
      subst hmac,
      apply exec_state.seq,
      repeat { sorry }
    }
  },
  repeat { sorry }
end

/-- order of exec_state can be changed if their ac's are distinct -/
lemma exec_state_comm_distinct_ac {s t u : state n σ τ} {ac₁ ac₂ : vector bool n} {k₁ k₂} :
  ac_distinct ac₁ ac₂ →
  exec_state k₁ ac₁ s t →
  exec_state k₂ ac₂ t u →
  ∃ t', exec_state k₂ ac₂ s t' ∧ exec_state k₁ ac₁ t' u :=
begin
  intros hd hk₁ hk₂,
  have hf₁ : _ := kernel_transform_inhab hk₁ sorry,
  have hf₂ : _ := kernel_transform_inhab hk₂ sorry,
  cases hf₁ with f₁ hf₁,
  cases hf₂ with f₂ hf₂,
  have h : u = state.map_active_threads ac₂ f₂ (state.map_active_threads ac₁ f₁ s) := begin
    have hkst : t = state.map_active_threads ac₁ f₁ s := ((hf₁ s t).mp hk₁), -- an underscore as a type would break the rw below
    have hktu : _ := (hf₂ t u).mp hk₂,
    rw ← hkst,
    exact hktu,
  end,
  rw state.map_active_threads_comm hd at h,
  apply exists.intro (state.map_active_threads ac₂ f₂ s),
  apply and.intro, 
  {
    apply (hf₂ _ _).mpr,
    refl,
  }, {
    apply (hf₁ _ _).mpr,
    exact h,
  }
end

@[simp]
lemma init_state_syncable {init : ℕ → σ} {f : memory τ → ℕ} {m : memory τ} : (init_state init f m).syncable m := begin
  unfold state.syncable init_state,
  simp,
end

lemma kernel_foldr_skip {k : kernel σ τ} {n} {ks s u} {ac : vector bool n} : exec_state (list.foldr kernel.seq k ks) ac s u = exec_state (list.foldr kernel.seq (kernel.compute id) ks ;; k) ac s u := sorry

end parlang