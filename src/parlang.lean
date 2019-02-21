import data.list.basic   -- basic operations on `list`
import data.option.basic -- basic operations on `option`
import logic.function    -- function update and inverses

namespace parlang
variables {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

/- TODO:

* add `active` to `thread_state`

* `loop : (σ → bool) → kernel → kernel`

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
inductive kernel (σ ι : Type) (τ : ι → Type) : Type
| load       : (σ → (Σi:ι, (τ i → σ))) → kernel
| store      : (σ → (Σi:ι, τ i)) → kernel
| compute {} : (σ → σ) → kernel
| seq        : kernel → kernel → kernel
| loop       : (σ → ℕ) → kernel → kernel
| sync {}    : kernel

open kernel

/-- Memory view -/
def memory (ι : Type) (τ : ι → Type) := Π (i : ι), τ i

namespace memory

def get (i : ι) (m : memory ι τ) : τ i := m i

def update (i : ι) (v : τ i) (m : memory ι τ) : memory ι τ := function.update m i v

end memory

/-- Thread state inclusing a global memory *view*, the list of loads and stores tells what should
differ between differnet threads. -/
structure thread_state (σ ι : Type) (τ : ι → Type) : Type :=
(state  : σ)
(global : memory ι τ)
(loads  : set ι := ∅)
(stores : set ι := ∅)

namespace thread_state

def load (f : σ → (Σi:ι, (τ i → σ))) (t : thread_state σ ι τ) : thread_state σ ι τ :=
let ⟨i, tr⟩ := f t.state in
{ state := tr (t.global.get i),
  loads := insert i t.loads,
  .. t }

def store (f : σ → (Σi:ι, τ i)) (t : thread_state σ ι τ) : thread_state σ ι τ :=
let ⟨i, v⟩ := f t.state in
{ global := t.global.update i v,
  stores := insert i t.stores,
  .. t}

def map (f : σ → σ) (t : thread_state σ ι τ) : thread_state σ ι τ :=
{ state := f t.state,
  .. t}

def sync (g : memory ι τ) (t : thread_state σ ι τ) : thread_state σ ι τ :=
{ global := g,
  loads := ∅,
  stores := ∅,
  .. t}

def accesses (t : thread_state σ ι τ) : set ι := t.stores ∪ t.loads

end thread_state

/-- Global program state -/
structure state (σ ι : Type) (τ : ι → Type) : Type :=
(threads : list (thread_state σ ι τ))

namespace state

def th (s : state σ ι τ) {t : ℕ} (h : t < s.threads.length) : thread_state σ ι τ :=
(s.threads.nth_le t h)

def map_threads (f : thread_state σ ι τ → thread_state σ ι τ) (s : state σ ι τ) : state σ ι τ :=
{ threads := s.threads.map f }

def syncable (s : state σ ι τ) (m : memory ι τ) : Prop :=
∀i:ι,
  (∀t∈s.threads, i ∉ (t : thread_state _ _ _).stores ∧ m i = t.global i) ∨
  (∃t (h : t < s.threads.length), i ∈ (s.th h).stores ∧ m i = (s.th h).global i ∧
    (∀t' (h' : t' < s.threads.length), t ≠ t' → i ∉ (s.th h).accesses))

end state

/-- Execute a kernel on a global state, i.e. a list of threads -/
inductive exec : kernel σ ι τ → state σ ι τ → state σ ι τ → Prop
| load (f) (s : state σ ι τ) :
  exec (load f) s (s.map_threads $ thread_state.load f)
| store (f) (s : state σ ι τ) :
  exec (store f) s (s.map_threads $ thread_state.store f)
| compute (f : σ → σ) (s : state σ ι τ) :
  exec (compute f) s (s.map_threads $ thread_state.map f)
| sync (s : state σ ι τ) (m : memory ι τ) (h : s.syncable m) :
  exec sync s (s.map_threads $ thread_state.sync m)
| seq (s t u : state σ ι τ) (k₁ k₂ : kernel σ ι τ) :
  exec k₁ s t → exec k₂ t u → exec (seq k₁ k₂) s u
| loop_stop (s : state σ ι τ) (f : σ → ℕ) (k : kernel σ ι τ) :
  (∀t∈s.threads, f (t:thread_state σ ι τ).state = 0) → exec (loop f k) s s
| loop_step (s t u : state σ ι τ) (f : σ → ℕ) (k : kernel σ ι τ) (c : ℕ) :
  (∀t∈s.threads, f (t:thread_state σ ι τ).state > 0) →
  exec k s t → exec (loop f k) t u → exec (loop f k) s u

end parlang