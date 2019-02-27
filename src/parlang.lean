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
          apply set_aux.union_no_mem_left this,
        end,
        contradiction,
      end,
      subst hleq,
    }
  }
end

end state

def no_thread_active (ac : vector bool n) : bool := ¬ac.to_list.any id
def any_thread_active (ac : vector bool n) : bool := ac.to_list.any id
def all_threads_active (ac : vector bool n) : bool := ac.to_list.all id

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

lemma all_threads_active_nth_zero (ac : vector bool (nat.succ n)) : all_threads_active ac → ac.nth 0 := begin
  cases ac,
  cases ac_val,
  case list.nil {
    have : list.length (@list.nil bool) = 0 := by rw list.length,
    contradiction,
  },
  case list.cons {
    rw vector.nth_zero,
    rw all_threads_active,
    rw list.all,
    simp,
    intros h _,
    rw vector.head,
    assumption,
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
    sorry -- TODO simplify and generalize proofs on vectors
  }
end

def deactivate_threads (f : σ → bool) (ac : vector bool n) (s : state n σ τ) : vector bool n := (ac.map₂ prod.mk s.threads).map (λ ⟨a, t⟩, if a then f t.tlocal else a)

/-- Execute a kernel on a global state, i.e. a list of threads -/
inductive exec_state {n : ℕ} : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop
| load (f) (s : state n σ τ) (ac : vector bool n) :
  exec_state (load f) ac s (s.map_active_threads ac $ thread_state.load f)
| store (f) (s : state n σ τ) (ac : vector bool n) :
  exec_state (store f) ac s (s.map_active_threads ac $ thread_state.store f)
| compute (f : σ → σ) (s : state n σ τ) (ac : vector bool n) :
  exec_state (compute f) ac s (s.map_active_threads ac $ thread_state.map f)
| sync_all (s : state n σ τ) (ac : vector bool n) (m : memory τ) (hs : s.syncable m) (ha : all_threads_active ac) :
  exec_state sync ac s (s.map_threads $ thread_state.sync m)
| sync_none (s : state n σ τ) (ac : vector bool n) (h : no_thread_active ac) :
  exec_state sync ac s s
| seq (s t u : state n σ τ) (ac : vector bool n) (k₁ k₂ : kernel σ τ) :
  exec_state k₁ ac s t → exec_state k₂ ac t u → exec_state (seq k₁ k₂) ac s u
| ite (s t u : state n σ τ) (ac : vector bool n) (f : σ → bool) (k₁ k₂ : kernel σ τ) :
  exec_state k₁ (deactivate_threads (bnot ∘ f) ac s) s t → exec_state k₂ (deactivate_threads f ac s) t u → exec_state (ite f k₁ k₂) ac s u -- in the then-branch we deactive those threads where the condition is false and vice versa
| loop_stop (s : state n σ τ) (ac : vector bool n) (f : σ → bool) (k : kernel σ τ) :
  (no_thread_active (deactivate_threads (bnot ∘ f) ac s)) → exec_state (loop f k) ac s s
| loop_step (s t u : state n σ τ) (ac : vector bool n) (f : σ → bool) (k : kernel σ τ) :
  (any_thread_active (deactivate_threads (bnot ∘ f) ac s)) →
  exec_state k (deactivate_threads (bnot ∘ f) ac s) s t → exec_state (loop f k) (deactivate_threads (bnot ∘ f) ac s) t u → exec_state (loop f k) ac s u

lemma exec_state_unique {s u t : state n σ τ} {ac : vector bool n} {k} (h₁ : exec_state k ac s u) (h₂ : exec_state k ac s t) (hl : 0 < n) : t = u := begin
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
      have : h₁_m = h₂_m := by apply state.syncable_unique h₁_hs h₂_hs hl,
      subst this,
      refl,
    },
    case parlang.exec_state.sync_none {
      apply false.elim (no_threads_active_not_all_threads hl h₂_h h₁_ha),
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

inductive exec_memory (ac : vector bool n) (k : kernel σ τ) (s : state n σ τ) (m : memory τ) : Prop
| intro (u) (hk : exec_state k ac s u) (syncable : u.syncable m) : exec_memory

end parlang