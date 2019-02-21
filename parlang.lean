import data.list.basic   -- basic operations on `list`
import data.option.basic -- basic operations on `option`
import logic.function    -- function update and inverses

namespace parlang
variables {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

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
inductive kernel (σ : Type) {ι : Type} (τ : ι → Type) : Type
| load       : (σ → Σi, τ i → σ) → kernel
| store      : (σ → Σi, τ i) → kernel
| compute {} : (σ → σ) → kernel
| seq        : kernel → kernel → kernel
| loop       : (σ → ℕ) → kernel → kernel
-- | loop       : (σ → bool) → kernel → kernel
-- | ite        : (σ → bool) → kernel → kernel → kernel
| sync {}    : kernel

open kernel

/-- Memory view -/
def memory {ι : Type} (τ : ι → Type) := Πi, τ i

namespace memory

def get (i : ι) (m : memory τ) : τ i := m i

def update (i : ι) (v : τ i) (m : memory τ) : memory τ := function.update m i v

end memory

/-- Thread state inclusing a global memory *view*, the list of loads and stores tells what should
differ between differnet threads. -/
structure thread_state (σ : Type) {ι : Type} (τ : ι → Type) : Type :=
(state  : σ)
(global : memory τ)
-- active : bool
(loads  : list ι)
(stores : list ι)

namespace thread_state

def load (i : σ → ι) (f : τ → σ → σ) (t : thread_state σ τ) : thread_state σ τ :=
let i := i t.state in
{ state := f (t.global.get i) t.state,
  loads := i :: t.loads,
  .. t }

def store (i : σ → Σi, τ i) (t : thread_state σ τ) : thread_state σ τ :=
let ⟨i, v⟩ := i t.state in
{ global := t.global.update i v,
  stores := i :: t.stores,
  .. t}

def map (f : σ → σ) (t : thread_state σ τ) : thread_state σ τ :=
{ state := f t.state,
  .. t}

def sync (g : memory τ) (t : thread_state σ τ) : thread_state σ τ :=
{ global := g,
  loads := [],
  stores := [],
  .. t}

def accesses (t : thread_state σ τ) : list ι := t.stores ++ t.loads

end thread_state

/-- Global program state -/
structure state (σ : Type) {ι : Type} (τ : ι → Type) : Type :=
(threads : list (thread_state σ τ))

namespace state

def th (s : state σ τ) {t : ℕ} (h : t < s.threads.length) : thread_state σ τ :=
(s.threads.nth_le t h)

def map_threads (f : thread_state σ τ → thread_state σ τ) (s : state σ τ) : state σ τ :=
{ threads := s.threads.map f, .. s}

def syncable (s : state σ τ) (m : memory ι τ) : Prop :=
∀i:ι,
  (∀t∈s.threads, i ∉ (t : thread_state _ _ _).stores ∧ m i = t.global i) ∨
  (∃t (h : t < s.threads.length), i ∈ (s.th h).stores ∧ m i = (s.th h).global i ∧
    (∀t' (h' : t' < s.threads.length), t ≠ t' → i ∉ (s.th h).accesses))

end state

/-- Execute a kernel on a global state, i.e. list of threads -/
inductive exec : kernel σ τ → state σ τ → state σ τ → Prop
| load (i : σ → ι) (f : τ → σ → σ) (s : state σ τ) :
  exec (load i f) s (s.map_threads $ thread_state.load i f)
| store (i : σ → ι × τ) (s : state σ τ) :
  exec (store i) s (s.map_threads $ thread_state.store i)
| compute (f : σ → σ) (s : state σ τ) :
  exec (compute f) s (s.map_threads $ thread_state.map f)
| sync (s : state σ τ) (m : memory ι τ) (h : s.syncable m) :
  exec sync s (s.map_threads $ thread_state.sync m)
| seq (s t u : state σ τ) (k₁ k₂ : kernel σ τ) :
  exec k₁ s t → exec k₂ t u → exec (seq k₁ k₂) s u
| loop_stop (s : state σ τ) (f : σ → ℕ) (k : kernel σ τ) :
  (∀t∈s.threads, f (t:thread_state σ τ).state = 0) → exec (loop f k) s s
| loop_step (s t u : state σ τ) (f : σ → ℕ) (k : kernel σ τ) (c : ℕ) :
  (∀t∈s.threads, f (t:thread_state σ τ).state > 0) →
  exec k s t → exec (loop f k) t u → exec (loop f k) s u

/-

exec : memory → [σ] → kernel → memory → Prop


-/


end parlang