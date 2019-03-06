import data.list.basic   -- basic operations on `list`
import data.option.basic -- basic operations on `option`
import data.set.basic
import data.vector
import data.vector2
import logic.function    -- function update and inverses
import aux

namespace parlang
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

/- TODO:

* add `active` to `thread_state`

* make vars implicit

-/


/-
We use the following conventions for type variables:

 `σ` -- thread internal states
 `ι` -- global memory index
 `τ` -- global memory values

-/

/-- Kernel of a parallel program.

The general idea is to not have explicit expressions, but use Lean functions to compute values. What
we are explicit global loads and stores.
-/
inductive kernel {ι : Type} (σ : Type) (τ : ι → Type) : Type
| load       : (σ → (Σi:ι, (τ i → σ))) → kernel
| store      : (σ → (Σi:ι, τ i)) → kernel
| compute {} : (σ → σ) → kernel
| seq        : kernel → kernel → kernel
| ite        : (σ → bool) → kernel → kernel → kernel
| loop       : (σ → bool) → kernel → kernel
| sync {}    : kernel

infixr ` ;; `:90 := kernel.seq
open kernel

/-- Memory view -/
def memory {ι : Type} (τ : ι → Type) := Π (i : ι), τ i

namespace memory

def get (i : ι) (m : memory τ) : τ i := m i

def update (i : ι) (v : τ i) (m : memory τ) : memory τ := function.update m i v

end memory

/-- Thread state inclusing a global memory *view*, the list of loads and stores tells what should
differ between differnet threads. -/
structure thread_state {ι : Type} (σ : Type) (τ : ι → Type) : Type :=
(tlocal : σ)
(global : memory τ)
(loads  : set ι := ∅)
(stores : set ι := ∅)

namespace thread_state

def load (f : σ → (Σi:ι, (τ i → σ))) (t : thread_state σ τ) : thread_state σ τ :=
let ⟨i, tr⟩ := f t.tlocal in
{ tlocal := tr (t.global.get i),
  loads := insert i t.loads,
  .. t }

def store (f : σ → (Σi:ι, τ i)) (t : thread_state σ τ) : thread_state σ τ :=
let ⟨i, v⟩ := f t.tlocal in
{ global := t.global.update i v,
  stores := insert i t.stores,
  .. t}

def map (f : σ → σ) (t : thread_state σ τ) : thread_state σ τ :=
{ tlocal := f t.tlocal,
  .. t}

def sync (g : memory τ) (t : thread_state σ τ) : thread_state σ τ :=
{ global := g,
  loads := ∅,
  stores := ∅,
  .. t}

def accesses (t : thread_state σ τ) : set ι := t.stores ∪ t.loads

end thread_state

def no_thread_active (ac : vector bool n) : bool := ¬ac.to_list.any id
def any_thread_active (ac : vector bool n) : bool := ac.to_list.any id
def all_threads_active (ac : vector bool n) : bool := ac.to_list.all id
def ac_distinct (ac₁ ac₂ : vector bool n) : Prop := ∀ (i : fin n), ac₁.nth i ≠ ac₂.nth i

/-- Global program state -/
structure state {ι : Type} (n : ℕ) (σ : Type) (τ : ι → Type) : Type :=
(threads : vector (thread_state σ τ) n)

namespace state

def map_threads (f : thread_state σ τ → thread_state σ τ) (s : state n σ τ) : state n σ τ :=
{ threads := s.threads.map f, ..s }

def map_active_threads (ac : vector bool n) (f : thread_state σ τ → thread_state σ τ) (s : state n σ τ) : state n σ τ :=
{ threads := (s.threads.map₂ (λ t (a : bool), if a then f t else t) ac), ..s }

def active_threads (ac : vector bool n) (s : state n σ τ) : list (thread_state σ τ) :=
((s.threads.map₂ prod.mk ac).to_list.filter (λ c : (thread_state σ τ × bool), c.2)).map (λ ⟨t, a⟩, t)

-- case 1: no thread changed ι and shadows must be equal at ι
-- case 2: thread t changed ι and all other threads must not access ι
def syncable (s : state n σ τ) (m : memory τ) : Prop :=
∀i:ι,
  (∀t∈s.threads, i ∉ (t : thread_state _ _).stores ∧ m i = t.global i) ∨
  (∃t (h : t < n), i ∈ (s.threads.nth ⟨t, h⟩).stores ∧ m i = (s.threads.nth ⟨t, h⟩).global i ∧
    (∀t' (h' : t' < n), t ≠ t' → i ∉ (s.threads.nth ⟨t, h⟩).accesses))

def precedes (s u : state n σ τ) : Prop :=
∀ (t : thread_state σ τ × thread_state σ τ), t ∈ (s.threads.map₂ prod.mk u.threads) → t.1.stores ⊆ t.2.stores ∧ t.1.loads ⊆ t.2.loads

-- we have to prove all four combinations (2 by contradiction and 2 because they match)
-- there must be at least one thread otherwise memory can be arbitrary
lemma syncable_unique {s : state n σ τ} {m m'} (h₁ : syncable s m) (h₂ : syncable s m') (hl : 0 < n) : m = m' := begin
  funext,
  specialize h₁ x,
  specialize h₂ x,
  cases h₁,
  case or.inl {
    cases h₂,
    case or.inl {
      have i : fin n := ⟨0, hl⟩,
      specialize h₁ (s.threads.nth i) vector.contains_nth,
      specialize h₂ (s.threads.nth i) vector.contains_nth,
      rw h₁.right,
      rw h₂.right,
    },
    case or.inr {
      cases h₂ with i h₂,
      cases h₂ with h₂_hl h₂,
      specialize h₁ (s.threads.nth ⟨i, h₂_hl⟩) vector.contains_nth,
      have : x ∈ (s.threads.nth ⟨i, h₂_hl⟩).stores := by apply h₂.left,
      have : x ∉ (s.threads.nth ⟨i, h₂_hl⟩).stores := by apply h₁.left,
      contradiction,
    }
  },
  case or.inr {
    cases h₁ with h₁l h₁,
    cases h₁ with h₁_hl h₁,
    cases h₁ with h₁_1 h₁,
    cases h₁ with h₁_2 h₁_3,
    cases h₂,
    case or.inl {
      specialize h₂ (s.threads.nth ⟨h₁l, h₁_hl⟩) vector.contains_nth,
      have : x ∉ (vector.nth (s.threads) ⟨h₁l, h₁_hl⟩).stores := by apply h₂.left,
      contradiction,
    },
    case or.inr {
      cases h₂ with h₂l h₂,
      cases h₂ with h₂_hl h₂,
      cases h₂ with h₂_1 h₂,
      cases h₂ with h₂_2 h₂_3,
      rw h₁_2,
      rw h₂_2,
      have hleq : h₁l = h₂l := begin
        by_contra hlneq,
        have : x ∉ thread_state.accesses (vector.nth (s.threads) ⟨h₁l, h₁_hl⟩) := begin
          specialize h₁_3 h₂l,
          apply h₁_3 h₂_hl hlneq,
        end,
        unfold thread_state.accesses at this,
        have : x ∉ (vector.nth (s.threads) ⟨h₁l, h₁_hl⟩).stores := begin
          apply set.union_no_mem_left this,
        end,
        contradiction,
      end,
      subst hleq,
    }
  }
end

lemma state_eq_per_thread {s u : state n σ τ} : (∀ i, s.threads.nth i = u.threads.nth i) → s = u := begin
  intros hieq,
  cases s,
  cases u,
  simp at *,
  apply vector.eq_element_wise hieq,
end

lemma map_active_threads_nth {s : state n σ τ} {ac : vector bool n} {f i} : ¬ ac.nth i → s.threads.nth i = (s.map_active_threads ac f).threads.nth i := begin
  intro hnac,
  unfold map_active_threads,
  simp [hnac],
end

lemma ac_distinct_cases {ac₁ ac₂ : vector bool n} (h : ac_distinct ac₁ ac₂) (i : fin n) : 
  (ac₁.nth i ∧ ¬ac₂.nth i) ∨ (ac₂.nth i ∧ ¬ac₁.nth i) ∨ (¬ac₁.nth i ∧ ¬ac₂.nth i) := begin
  unfold ac_distinct at h,
  by_cases h1 : ↥(vector.nth ac₁ i),
  {
    left,
    specialize h i,
    simp [h1] at h,
    apply and.intro,
    { assumption, },
    {
      intro,
      apply h,
      sorry,
    }
  }, {
    by_cases h2 : ↥(vector.nth ac₂ i),
    {
      right,
      left,
      sorry,
    }, {
      right,
      right,
      exact ⟨h1, h2⟩,
    }
  }
end

lemma map_active_threads_comm {s : state n σ τ} {ac₁ ac₂ : vector bool n} {f g} (h : ac_distinct ac₁ ac₂) : 
  (s.map_active_threads ac₁ f).map_active_threads ac₂ g = (s.map_active_threads ac₂ g).map_active_threads ac₁ f := begin
  simp [map_active_threads],
  apply vector.eq_element_wise,
  intro i,
  repeat { rw vector.nth_map₂},
  cases (ac_distinct_cases h i),
  {
    simp[h_1],
  }, {
    cases h_1,
    {
      simp[h_1],
    }, {
      simp[h_1],
    }
  }
end

end state

lemma no_threads_active_nth_zero (ac : vector bool (nat.succ n)) : no_thread_active ac → ¬ac.nth 0 := begin
  cases ac,
  cases ac_val,
  case list.nil {
    sorry, --contr
  },
  case list.cons {
    rw vector.nth_zero,
    rw no_thread_active,
    rw list.any,
    simp,
    rw vector.head,
    intro h,
    by_contra,
    apply h,
    left,
    sorry, -- should be trivial
  }
end

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
    sorry -- TODO simplify and generalize proofs on vectors
  }
end

def deactivate_threads (f : σ → bool) (ac : vector bool n) (s : state n σ τ) : vector bool n := (ac.map₂ prod.mk s.threads).map (λ ⟨a, t⟩, (bnot ∘ f) t.tlocal && a)

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

/-- Execute a kernel on a global state, i.e. a list of threads -/
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
  exec_state (loop f k) (deactivate_threads (bnot ∘ f) ac s) t u →
  exec_state (loop f k) ac s u

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
      apply false.elim (no_threads_active_not_all_threads hl h₁_h h₂_ha),
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
          rw vector.map₂_nil',
          rw vector.map₂_nil,
          intro,
          have : (a, b) ∉ (@vector.nil (thread_state σ τ × thread_state σ τ)) := by apply vector.mem_nil,
          contradiction,
        end
      end,
    },
    case nat.succ {
      exact match ac, s.threads with
      | ⟨list.cons a ac_tl, h ⟩ := begin

        end
      end,
    },

    unfold thread_state.load,
  }
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
    apply state.map_active_threads_nth hna,
  },
  case parlang.exec_state.store {
    apply state.map_active_threads_nth hna,
  },
  case parlang.exec_state.compute {
    apply state.map_active_threads_nth hna,
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

def kernel_transform_func (k) (f) : Prop := ∀ (n) (s u : state n σ τ) (ac : vector bool n), exec_state k ac s u ↔ u = s.map_active_threads ac f

lemma kernel_transform_inhab (k : kernel σ τ) : ∃ f, kernel_transform_func k f := begin
  unfold kernel_transform_func,
  cases k,
  case parlang.kernel.load {
    apply exists.intro (thread_state.load k),
    intros n s u ac,
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
    apply exists.intro id,
    intros n s u ac,
    apply iff.intro,
    {
      intro he,
      cases he,
      case parlang.exec_state.sync_all {
        simp [state.map_active_threads],
        sorry, -- need some nice aux lemma for map₂
      },
      case parlang.exec_state.sync_none {
        sorry,
      },
    }, {
      intro hm,
      subst hm,
      apply exec_state.sync_none,
    }
  }
end

lemma exec_state_comm_distinct_ac {s t u : state n σ τ} {ac₁ ac₂ : vector bool n} {k₁ k₂} :
  ac_distinct ac₁ ac₂ →
  exec_state k₁ ac₁ s t →
  exec_state k₂ ac₂ t u →
  ∃ t', exec_state k₂ ac₂ s t' ∧ exec_state k₁ ac₁ t' u :=
begin
  intros hd hk₁ hk₂,
  have hf₁ : _ := kernel_transform_inhab k₁,
  have hf₂ : _ := kernel_transform_inhab k₂,
  cases hf₁ with f₁ hf₁,
  cases hf₂ with f₂ hf₂,
  have h : u = state.map_active_threads ac₂ f₂ (state.map_active_threads ac₁ f₁ s) := begin
    have hkst : t = state.map_active_threads ac₁ f₁ s := ((hf₁ n s t ac₁).mp hk₁), -- an underscore as a type would break the rw below
    have hktu : _ := (hf₂ n t u ac₂).mp hk₂,
    rw ← hkst,
    exact hktu,
  end,
  rw state.map_active_threads_comm hd at h,
  apply exists.intro (state.map_active_threads ac₂ f₂ s),
  apply and.intro, 
  {
    apply (hf₂ n _ _ _).mpr,
    refl,
  }, {
    apply (hf₁ n _ _ _).mpr,
    exact h,
  }
end

inductive exec_memory (k : kernel σ τ) (ac : vector bool n) (s : state n σ τ) (m m' : memory τ) : Prop
| intro {u} (hk : exec_state k ac (s.map_threads $ thread_state.sync m) u) (syncable : u.syncable m') : exec_memory

lemma exec_memory_unique {s : state n σ τ} {m o o': memory τ} {ac : vector bool n} {k} (h₁ : exec_memory k ac s m o) (h₂ : exec_memory k ac s m o') (hl : 0 < n) : o = o' := begin
  cases h₁,
  cases h₂,
  have : h₂_u = h₁_u := by apply exec_state_unique h₁_hk h₂_hk hl,
  subst this,
  apply state.syncable_unique h₁_syncable h₂_syncable hl,
end

lemma exec_memory_seq_left {k₁ k₂ : kernel σ τ} {ac : vector bool n} {s} {m o} : exec_memory (k₁ ;; k₂) ac s m o → ∃r, exec_memory k₁ ac s m r := begin
  intro he,
  cases he,
  have hesk₁ : _ := by apply exec_state_seq_left he_hk,
  cases hesk₁ with t hesk₁,
  have hk₁s : ∃r, t.syncable r := begin

  end,
  cases hk₁s with r,
  apply Exists.intro r,
  apply exec_memory.intro hesk₁ hk₁s_h,
end

end parlang