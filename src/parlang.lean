import data.list.basic   -- basic operations on `list`
import data.option.basic -- basic operations on `option`
import data.set.basic
import data.vector
import logic.function    -- function update and inverses
import aux

namespace parlang
variables {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

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
structure state {ι : Type} (σ : Type) (τ : ι → Type) : Type :=
(threads : list (thread_state σ τ))

namespace state

def th (s : state σ τ) {t : ℕ} (h : t < s.threads.length) : thread_state σ τ :=
(s.threads.nth_le t h)

lemma th_mem (s : state σ τ) {ts : thread_state σ τ} {t : ℕ} (hl : t < s.threads.length) (h : th s hl = ts) : ts ∈ s.threads := sorry
-- begin
--   have h_hdtl : ∃ x xs, s.threads = (x :: xs) := begin
--     apply list_aux.list_length_neq_zero,
--     apply nat_aux.lt_neq_zeor t,
--     assumption,
--   end,
--   cases h_hdtl with ts' h_hdtl,
--   cases h_hdtl with tail heq,
--   induction t,
--   case nat.zero {
--     have : ts = ts' := begin
--       rw ← h,
--       rw heq at hl,
--       rw th,
--       sorry,
--     end,
--     rw this,
--     rw heq,
--     simp,
--   },
--   case nat.succ {
--     by_cases hleq : t_n < list.length (s.threads),
--     {
--       apply t_ih hleq,
--       assumption,
--     }, {

--     }
--   }
-- end

def map_threads (f : thread_state σ τ → thread_state σ τ) (s : state σ τ) : state σ τ :=
{ threads := s.threads.map f, ..s }

def map_active_threads (ac : list bool) (f : thread_state σ τ → thread_state σ τ) (s : state σ τ) : state σ τ :=
{ threads := (s.threads.zip ac).map (λ ⟨t, a⟩, if a then f t else t), ..s }

def active_threads (ac : list bool) (s : state σ τ) : list (thread_state σ τ) :=
((s.threads.zip ac).filter (λ c : (thread_state σ τ × bool), c.2)).map (λ ⟨t, a⟩, t)

-- case 1: no thread changed ι and shadows must be equal at ι
-- case 2: thread t changed ι and all other threads must not access ι
def syncable (s : state σ τ) (m : memory τ) : Prop :=
∀i:ι,
  (∀t∈s.threads, i ∉ (t : thread_state _ _).stores ∧ m i = t.global i) ∨
  (∃t (h : t < s.threads.length), i ∈ (s.th h).stores ∧ m i = (s.th h).global i ∧
    (∀t' (h' : t' < s.threads.length), t ≠ t' → i ∉ (s.th h).accesses))

-- we have to prove all four combinations (2 by contradiction and 2 because they match)
-- there must be at least one thread otherwise memory can be arbitrary
lemma syncable_unique (s : state σ τ) (m m') (h₁ : syncable s m) (h₂ : syncable s m') (hl : s.threads.length ≠ 0) : m = m' := begin
  funext,
  specialize h₁ x,
  specialize h₂ x,
  cases h₁,
  case or.inl {
    cases h₂,
    case or.inl {
      have : ∃ x xs, s.threads = (x :: xs) := by apply list_aux.list_length_neq_zero hl,
      cases this with head this,
      cases this with tail eq,
      have : head ∈ s.threads := begin
        unfold has_mem.mem,
        rw eq,
        rw list.mem,
        simp,
      end,
      specialize h₁ head this,
      specialize h₂ head this,
      rw h₁.right,
      rw h₂.right,
    },
    case or.inr {
      cases h₂ with n h₂,
      cases h₂ with h₂_hl h₂,
      generalize_hyp heq : (th s h₂_hl) = ts at h₂,
      specialize h₁ ts,
      specialize h₁ _,
      {
        have : x ∈ ts.stores := begin
          apply h₂.left,
        end,
        have : x ∉ ts.stores := begin
          apply h₁.left,
        end,
        contradiction,
      },
      {
        apply th_mem s h₂_hl heq,
      }
    }
  },
  case or.inr {
    cases h₁ with h₁l h₁,
    cases h₁ with h₁_hl h₁,
    cases h₁ with h₁_1 h₁,
    cases h₁ with h₁_2 h₁_3,
    cases h₂,
    case or.inl {
      generalize_hyp htseq : (th s h₁_hl) = ts at h₁_1 h₁_2 h₁_3,
      specialize h₂ ts,
      have : x ∉ ts.stores := begin
        suffices : x ∉ ts.stores ∧ m' x = ts.global x,
        cases this,
        assumption,
        apply h₂,
        apply th_mem s h₁_hl,
        assumption,
      end,
      contradiction,
    },
    case or.inr {
      cases h₂ with h₂l h₂,
      cases h₂ with h₂_hl h₂,
      cases h₂ with h₂_1 h₂,
      cases h₂ with h₂_2 h₂_3,
      rw h₁_2,
      rw h₂_2,
      by_cases hleq : h₁l = h₂l, -- thread id's must be equal otherwise contradiction
      {
        subst hleq,
      }, {
        have : x ∉ thread_state.accesses (th s h₁_hl) := begin
          specialize h₁_3 h₂l,
          apply h₁_3 h₂_hl hleq,
        end,
        unfold thread_state.accesses at this,
        have : x ∉ (th s h₁_hl).stores := begin
          apply set_aux.union_no_mem_left this,
        end,
        contradiction,
      },
    }
  }
end

end state

def no_thread_active (ac : list bool) : bool := ¬ac.any id

def all_threads_active (ac : list bool) : bool := ac.all id

def deactivate_threads (f : σ → bool) (ac : list bool) (s : state σ τ) : list bool := (ac.zip s.threads).map (λ ⟨a, t⟩, if a then f t.tlocal else a)

/-- Execute a kernel on a global state, i.e. a list of threads -/
inductive exec_state (n : ℕ) : kernel σ τ → list bool → state σ τ → state σ τ → Prop
| load (f) (s : state σ τ) (a : list bool) :
  exec_state (load f) a s (s.map_active_threads a $ thread_state.load f)
| store (f) (s : state σ τ) (a : list bool) :
  exec_state (store f) a s (s.map_active_threads a $ thread_state.store f)
| compute (f : σ → σ) (s : state σ τ) (a : list bool) :
  exec_state (compute f) a s (s.map_active_threads a $ thread_state.map f)
| sync_all (s : state σ τ) (a : list bool) (m : memory τ) (hs : s.syncable m) (ha : all_threads_active a) :
  exec_state sync a s (s.map_threads $ thread_state.sync m)
| sync_none (s : state σ τ) (a : list bool) (h : no_thread_active a) :
  exec_state sync a s s
| seq (s t u : state σ τ) (a : list bool) (k₁ k₂ : kernel σ τ) :
  exec_state k₁ a s t → exec_state k₂ a t u → exec_state (seq k₁ k₂) a s u
| ite (s t u : state σ τ) (a : list bool) (f : σ → bool) (k₁ k₂ : kernel σ τ) :
  exec_state k₁ (deactivate_threads (bnot ∘ f) a s) s t → exec_state k₂ (deactivate_threads f a s) t u → exec_state (ite f k₁ k₂) a s u -- in the then-branch we deactive those threads where the condition is false and vice versa
| loop_stop (s : state σ τ) (a : list bool) (f : σ → bool) (k : kernel σ τ) :
  (∀t ∈ s.active_threads a, ¬f (t:thread_state σ τ).tlocal) → exec_state (loop f k) a s s
| loop_step (s t u : state σ τ) (a : list bool) (f : σ → bool) (k : kernel σ τ) :
  (∃t∈s.active_threads a, f (t:thread_state σ τ).tlocal) →
  exec_state k (deactivate_threads (bnot ∘ f) a s) s t → exec_state (loop f k) (deactivate_threads (bnot ∘ f) a s) t u → exec_state (loop f k) a s u

lemma exec_state_unique {s u t : state σ τ} {k} (h₁ : exec_state k s u) (h₂ : exec_state k s t) : t = u := begin
  induction h₁,
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
    
  }
  
end

inductive exec_memory (k : kernel σ τ) (s : state σ τ) (m : memory τ) : Prop
| intro (u) (hk : exec_state k s u) (syncable : u.syncable m) : exec_memory

end parlang