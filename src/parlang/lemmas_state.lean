import parlang.defs
import parlang.lemmas_active_map
import parlang.lemmas_thread_state

namespace parlang
namespace state
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

-- we have to prove all four combinations (2 by contradiction and 2 because they match)
-- there must be at least one thread otherwise memory can be arbitrary
-- todo: do pattern matching to shorten proof?
lemma syncable_unique {s : state n σ τ} {m m'} (h₁ : syncable s m) (h₂ : syncable s m') (hl : 0 < n) : m = m' := begin
  funext,
  specialize h₁ x,
  specialize h₂ x,
  cases h₁,
  case or.inl {
    cases h₂,
    case or.inl {
      have i : fin n := ⟨0, hl⟩,
      rw (h₁ i).right,
      rw (h₂ i).right,
    },
    case or.inr {
      cases h₂ with i h₂,
      specialize h₁ i,
      have : x ∈ (s.threads.nth i).stores := by apply h₂.left,
      have : x ∉ (s.threads.nth i).stores := by apply h₁.left,
      contradiction,
    }
  },
  case or.inr {
    cases h₁ with h₁l h₁,
    cases h₁ with h₁_1 h₁,
    cases h₁ with h₁_2 h₁_3,
    cases h₂,
    case or.inl {
      specialize h₂ h₁l,
      have : x ∉ (vector.nth (s.threads) h₁l).stores := by apply h₂.left,
      contradiction,
    },
    case or.inr {
      cases h₂ with h₂l h₂,
      cases h₂ with h₂_1 h₂,
      cases h₂ with h₂_2 h₂_3,
      rw h₁_2,
      rw h₂_2,
      have hleq : h₁l = h₂l := begin
        by_contra hlneq,
        have : x ∉ thread_state.accesses (vector.nth (s.threads) h₁l) := begin
          specialize h₂_3 h₁l,
          apply h₂_3,
          intro a,
          apply hlneq,
          exact eq.symm a,
        end,
        unfold thread_state.accesses at this,
        have : x ∉ (vector.nth (s.threads) h₁l).stores := begin
          apply set.union_no_mem_left this,
        end,
        contradiction,
      end,
      subst hleq,
    }
  }
end

theorem syncable_tlocal (s : state n σ τ) (m : memory τ) (ac : vector bool n) (tl : thread_state σ τ → σ) : s.syncable m ↔ (s.map_active_threads ac $ λts, { tlocal := tl ts, ..ts }).syncable m := begin
  unfold syncable,
  induction n,
  case nat.zero {
    split, {
      intro h,
      intro i,
      left,
      intro tid,
      apply fin_zero_elim tid,
    }, {
      intros h i,
      left,
      intro tid,
      apply fin_zero_elim tid,
    }
  },
  case nat.succ : n ih {
    split, {
      intros h i,
      specialize h i,
      cases h,
      {
        left,
        intro tid,
        specialize h tid,
        cases h,
        split, {
          sorry,
        },
        sorry
      },
      sorry,
    },
    sorry,
  }
end

@[simp]
lemma compute_stores_state {s : state n σ τ} {ac : vector bool n} {tid} {f g} : 
(vector.nth ((map_active_threads ac (thread_state.compute g ∘ f) s).threads) tid).stores = (vector.nth ((map_active_threads ac f s).threads) tid).stores := begin
  unfold map_active_threads,
  simp,
  by_cases h : vector.nth ac tid = tt, {
    simp [*, thread_state.compute],
  }, {
    simp at h,
    simp [*, thread_state.compute],
  }
end

@[simp]
lemma compute_loads_state {s : state n σ τ} {ac : vector bool n} {tid} {f g} : 
(vector.nth ((map_active_threads ac (thread_state.compute g ∘ f) s).threads) tid).loads = (vector.nth ((map_active_threads ac f s).threads) tid).loads := begin
  unfold map_active_threads,
  simp,
  by_cases h : vector.nth ac tid = tt, {
    simp [*, thread_state.compute],
  }, {
    simp at h,
    simp [*, thread_state.compute],
  }
end

@[simp]
lemma compute_shared_state {s : state n σ τ} {ac : vector bool n} {tid} {f g} : 
(vector.nth ((map_active_threads ac (thread_state.compute g ∘ f) s).threads) tid).shared = (vector.nth ((map_active_threads ac f s).threads) tid).shared := begin
  unfold map_active_threads,
  simp,
  by_cases h : vector.nth ac tid = tt, {
    simp [*, thread_state.compute],
  }, {
    simp at h,
    simp [*, thread_state.compute],
  }
end

@[simp]
lemma compute_access_state {s : state n σ τ} {ac : vector bool n} {tid} {f g} : 
thread_state.accesses (vector.nth ((map_active_threads ac (thread_state.compute g ∘ f) s).threads) tid) = thread_state.accesses (vector.nth ((map_active_threads ac f s).threads) tid) := by simp [thread_state.accesses]

@[simp]
lemma syncable_remove_compute {s : state n σ τ} (ac : vector bool n) (f m g) : syncable (map_active_threads ac (thread_state.compute g ∘ f) s) m ↔ syncable (map_active_threads ac f s) m := begin
  simp [syncable, compute_stores_state, compute_shared_state, compute_access_state],
end

lemma state_eq_per_thread {s u : state n σ τ} : (∀ i, s.threads.nth i = u.threads.nth i) → s = u := begin
  intros hieq,
  cases s,
  cases u,
  simp at *,
  apply vector.eq_element_wise hieq,
end

lemma map_active_threads_nth_inac {s : state n σ τ} {ac : vector bool n} {f i} : ¬ ac.nth i → s.threads.nth i = (s.map_active_threads ac f).threads.nth i := begin
  intro hnac,
  unfold map_active_threads,
  simp [hnac],
end

lemma map_active_threads_nth_ac {s : state n σ τ} {ac : vector bool n} {f i} : ac.nth i → (s.map_active_threads ac f).threads.nth i = f (s.threads.nth i) := begin
  intro hac,
  unfold map_active_threads,
  simp [hac],
end

@[simp]
lemma map_map_active_threads {s : state n σ τ} {ac : vector bool n} {f g} : (s.map_active_threads ac f).map_active_threads ac g  = s.map_active_threads ac (g ∘ f) := begin
  simp [map_active_threads],
  rw vector.map₂_map₂,
  apply vector.eq_element_wise,
  intro i,
  simp,
  by_cases h : vector.nth ac i = tt,
  { simp *, },
  { simp at h, simp *, },
end

lemma map_map_active_threads' {s : state n σ τ} {ac : vector bool n} (f g) : (s.map_active_threads ac f).map_active_threads ac g  = s.map_active_threads ac (λ ts, g (f ts)) := begin
  simp [map_active_threads],
  apply vector.eq_element_wise,
  intro,
  simp,
  by_cases h : vector.nth ac i = tt,
  { simp *, },
  { simp at h, simp *, },
end

lemma map_threads_all_threads_active {s : state n σ τ} {ac : vector bool n} {f} (h : all_threads_active ac) : s.map_threads f = s.map_active_threads ac f := begin
  simp [map_active_threads, map_threads],
  apply vector.eq_element_wise,
  intro,
  simp,
  by_cases h' : vector.nth ac i = tt,
  { simp *, },
  {
    unfold all_threads_active list.all at h,
    have : _ := all_threads_active_nth h i,
    contradiction,
  },
end

lemma map_active_threads_id (s : state n σ τ) (ac : vector bool n) : s = s.map_active_threads ac (thread_state.compute id) := begin
  cases s,
  simp [map_active_threads],
  apply vector.eq_element_wise,
  simp,
end

lemma map_active_threads_comm {s : state n σ τ} {ac₁ ac₂ : vector bool n} {f g} (h : ac_distinct ac₁ ac₂) : 
  (s.map_active_threads ac₁ f).map_active_threads ac₂ g = (s.map_active_threads ac₂ g).map_active_threads ac₁ f := begin
  simp [map_active_threads],
  apply vector.eq_element_wise,
  intro i,
  repeat { rw vector.nth_map₂},
  cases h i,
  {
    simp[h_1],
    by_cases vector.nth ac₂ i = tt,
    { rw h, },
    { simp at h, simp [h], }
  }, {
    simp[h_1],
    by_cases vector.nth ac₁ i = tt,
    { rw h, },
    { simp at h, simp [h], }
  }
end

lemma map_active_threads_no_thread_active (s : state n σ τ) (ac : vector bool n) (f) 
(h : no_thread_active ac) :
s.map_active_threads ac f = s := begin
  unfold map_active_threads,
  cases s,
  simp,
  apply vector.eq_element_wise,
  intro i,
  simp,
  by_cases h' : vector.nth ac i = tt,
  {
    have : _ := no_threads_active_nth h i,
    contradiction,
  }, {
    rw eq_ff_eq_not_eq_tt at h',
    simp *,
  }
end

end state
end parlang