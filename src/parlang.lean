import data.list.basic   -- basic operations on `list`
import data.option.basic -- basic operations on `option`
import logic.function    -- function update and inverses

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
(active : bool := tt)

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

def map_threads (f : thread_state σ τ → thread_state σ τ) (s : state σ τ) : state σ τ :=
{ threads := s.threads.map f, ..s }

def map_active_threads (f : thread_state σ τ → thread_state σ τ) (s : state σ τ) : state σ τ :=
s.map_threads (λ t, if t.active then f t else t)

def no_thread_active (s : state σ τ) : bool := ¬s.threads.any (λ t, t.active)

def all_threads_active (s : state σ τ) : bool := s.threads.all (λ t, t.active)

def active_threads (s : state σ τ) : list (thread_state σ τ) := s.threads.filter (λ t, t.active)

def deactive_threads (f : σ → bool) (s : state σ τ) := s.map_active_threads (λt, { active := f t.tlocal, ..t})

def mirror_active_threads (u : state σ τ) (s : state σ τ) : state σ τ := 
{ threads := s.threads.zip_with (λt t' : thread_state σ τ, { active := t'.active, ..t}) u.threads }

def syncable (s : state σ τ) (m : memory τ) : Prop :=
∀i:ι,
  (∀t∈s.threads, i ∉ (t : thread_state _ _).stores ∧ m i = t.global i) ∨
  (∃t (h : t < s.threads.length), i ∈ (s.th h).stores ∧ m i = (s.th h).global i ∧
    (∀t' (h' : t' < s.threads.length), t ≠ t' → i ∉ (s.th h).accesses))

end state

def bool_complement {α : Type} (f: α → bool) : α → bool := λa:α, ¬f a

/-- Execute a kernel on a global state, i.e. a list of threads -/
inductive exec_state : kernel σ τ → state σ τ → state σ τ → Prop
| load (f) (s : state σ τ) :
  exec_state (load f) s (s.map_active_threads $ thread_state.load f)
| store (f) (s : state σ τ) :
  exec_state (store f) s (s.map_active_threads $ thread_state.store f)
| compute (f : σ → σ) (s : state σ τ) :
  exec_state (compute f) s (s.map_active_threads $ thread_state.map f)
| sync_all (s : state σ τ) (m : memory τ) (hs : s.syncable m) (ha : s.all_threads_active) :
  exec_state sync s (s.map_threads $ thread_state.sync m)
| sync_none (s : state σ τ) (h : s.no_thread_active) :
  exec_state sync s s
| seq (s t u : state σ τ) (k₁ k₂ : kernel σ τ) :
  exec_state k₁ s t → exec_state k₂ t u → exec_state (seq k₁ k₂) s u
| ite (s t u : state σ τ) (f : σ → bool) (k₁ k₂ : kernel σ τ) :
  exec_state k₁ (s.deactive_threads (λl, ¬f l)) t → exec_state k₂ (t.deactive_threads f) u → exec_state (ite f k₁ k₂) s u -- in the then-branch we deactive those threads where the condition is false and vice versa
| loop_stop (s : state σ τ) (f : σ → bool) (k : kernel σ τ) :
  (∀t∈s.active_threads, ¬f (t:thread_state σ τ).tlocal) → exec_state (loop f k) s s
| loop_step (s t u : state σ τ) (f : σ → bool) (k : kernel σ τ) :
  (∃t∈s.active_threads, f (t:thread_state σ τ).tlocal) →
  exec_state k (s.deactive_threads (bool_complement f)) t → exec_state (loop f k) (t.deactive_threads (bool_complement f)) u → exec_state (loop f k) s (u.mirror_active_threads s) -- IS THIS CORRECT?

inductive exec_memory (k : kernel σ τ) (s : state σ τ) (m : memory τ) : Prop
| intro (u) (hk : exec_state k s u) (syncable : u.syncable m) : exec_memory

-- example {s u t : state σ ι τ} {k} (h₁ : exec_state k s u) (h₂ : exec_state k s t) : t = u := 

end parlang