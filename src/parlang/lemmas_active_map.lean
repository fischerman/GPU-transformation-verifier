import parlang.defs

namespace parlang
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

lemma all_threads_active_nth : ∀ {n} {ac : vector bool n}, all_threads_active ac → ∀ i, ac.nth i 
| 0 ⟨[], refl⟩ h i := by apply (vector.nat_le_zero i.is_lt).elim
| (n + 1) ⟨ a :: as, hp⟩ h ⟨i, hi⟩ := begin
  rw vector.nth,
  cases i,
  case nat.zero {
    simp [all_threads_active, vector.to_list, list.all] at h,
    exact h.left,
  },
  case nat.succ {
    simp,
    simp [all_threads_active, vector.to_list, list.all] at h,
    have hi' : i < n := begin
      rw [← nat.add_one, nat.add_comm i 1, nat.add_comm n 1] at hi,
      apply lt_of_add_lt_add_left hi,
    end,
    have hp' : list.length as = n := by exact nat.add_right_cancel hp,
    specialize @all_threads_active_nth n ⟨as, hp'⟩,
    simp [all_threads_active, list.all] at all_threads_active_nth,
    specialize all_threads_active_nth h.right ⟨i, hi'⟩,
    exact all_threads_active_nth,
  }
end

lemma all_threads_active_nth_zero (ac : vector bool (nat.succ n)) : all_threads_active ac → ac.nth 0
| h := all_threads_active_nth h 0

lemma no_threads_active_nth : ∀ {n} {ac : vector bool n}, no_thread_active ac → ∀ i, ¬ac.nth i
| n ⟨[], h'⟩ h tid := (by subst h'; apply fin_zero_elim tid)
| (n + 1) ⟨t :: ts, h'⟩ h ⟨tid, h''⟩ := begin
  simp [no_thread_active, vector.to_list, list.any, not_or_distrib] at h,
  cases tid,
  {
    simp [vector.nth, list.nth_le],
    exact h.left,
  }, {
    simp [vector.nth, list.nth_le],
    specialize @no_threads_active_nth n ⟨ts, nat.succ_inj h'⟩,
    simp [no_thread_active, list.any] at no_threads_active_nth,
    specialize no_threads_active_nth h.right ⟨tid, _⟩,
    exact no_threads_active_nth,
    exact nat.succ_lt_succ_iff.mp h'',
  }
end

lemma no_threads_active_nth_zero (ac : vector bool (nat.succ n)) : no_thread_active ac → ¬ac.nth 0
| h := no_threads_active_nth h 0

lemma all_threads_active_repeat (n : ℕ) : all_threads_active (vector.repeat tt n) := begin
  induction n,
  { rw vector.repeat, simp [all_threads_active], },
  {
    rw vector.repeat, 
    simp [all_threads_active],
    apply n_ih,
  }
end

lemma no_threads_active_not_all_threads {ac : vector bool n} (hl : 0 < n) : no_thread_active ac → ¬↥(all_threads_active ac) := begin
  cases n,
  case nat.zero {
    have : ¬ 0 < 0 := by simp,
    contradiction,
  },
  case nat.succ {
    intros a b,
    have : ↥(ac.nth ⟨0, hl⟩) := begin
      apply all_threads_active_nth_zero,
      assumption,
    end,
    have : ¬↥(ac.nth ⟨0, hl⟩) := begin
      apply no_threads_active_nth_zero,
      assumption,
    end,
    contradiction,
  },
end

lemma no_threads_active_no_active_thread {ac : vector bool n} : no_thread_active ac → ¬any_thread_active ac := begin
  induction n,
  case nat.zero {
    cases ac,
    cases ac_val,
    case list.nil {
      rw no_thread_active,
      rw any_thread_active,
      simp,
    },
    case list.cons {
      contradiction,
    }
  },
  case nat.succ {
    unfold no_thread_active any_thread_active,
    simp,
  }
end

lemma deactivate_threads_alive {f : σ → bool} {ac : vector bool n} {s : state n σ τ} {i} : (deactivate_threads f ac s).nth i → ac.nth i := begin
  intro hd,
  simp[deactivate_threads] at hd,
  exact hd.left,
end

lemma deactivate_threads_deactivate_inactive_thread {f : σ → bool} {ac : vector bool n} {s : state n σ τ} {i} : ¬ac.nth i → ¬(deactivate_threads f ac s).nth i
| a b := a (deactivate_threads_alive b) -- is there a more elegant way for contraposition?

lemma active_map_deactivate_threads {ac : vector bool n} {i} {f : σ → bool} {s : state n σ τ} : 
  ac.nth i → f (s.threads.nth i).tlocal → (deactivate_threads (bnot ∘ f) ac s).nth i := 
begin
  intros hac hf,
  simp [deactivate_threads],
  exact ⟨hac, hf⟩,
end

lemma active_map_deactivate_threads' {ac : vector bool n} {i} {f : σ → bool} {s : state n σ τ} : 
  ac.nth i → ¬f (s.threads.nth i).tlocal → (deactivate_threads f ac s).nth i := begin
  intros hac hf,
  simp [deactivate_threads],
  simp at hf,
  rw bool.bnot_ff,
  simp,
  exact ⟨hac, hf⟩,
end

lemma deactivate_threads_condition {f : σ → bool} {ac : vector bool n} {s : state n σ τ} {i} : 
vector.nth (deactivate_threads (bnot ∘ f) ac s) i → f ((vector.nth (s.threads) i).tlocal) := by simp [deactivate_threads]

lemma deactivate_threads_condition' {f : σ → bool} {ac : vector bool n} {s : state n σ τ} {i} : 
vector.nth (deactivate_threads (f) ac s) i → ¬f ((vector.nth (s.threads) i).tlocal) := begin
  simp [deactivate_threads],
  intros _ h,
  rw ← bnot_eq_true_eq_eq_ff,
  exact h,
end

lemma deactivate_threads_complement {f : σ → bool} {ac : vector bool n} {s : state n σ τ} {i} : 
  vector.nth (deactivate_threads (bnot ∘ f) ac s) i → ¬↥(vector.nth (deactivate_threads (f) ac s) i) := begin
  intro h,
  simp [deactivate_threads] at ⊢ h,
  intro _,
  cases h,
  apply h_right,
end

end parlang