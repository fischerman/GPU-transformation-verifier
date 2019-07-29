import data.list.basic   -- basic operations on `list`
import data.option.basic -- basic operations on `option`
import data.set.basic
import data.vector
import data.vector2
import logic.function    -- function update and inverses
import aux

namespace parlang
variables {n : ℕ} {σ : Type} {ι : Type} {τ : ι → Type} [decidable_eq ι]

/-
We use the following conventions for type variables:

 `σ` -- thread internal states
 `ι` -- global memory index
 `τ` -- global memory type map

-/

/-- Kernel of a parallel program.

The general idea is to not have explicit expressions, but use Lean functions to compute values. What
we are explicit global loads and stores.

Σ is constructor where the second argument may depend on the type of the first (in this case i). Can be constructed using ⟨...⟩
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

def get (m : memory τ) (i : ι) : τ i := m i

def update (m : memory τ) (i : ι) (v : τ i) : memory τ := function.update m i v

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

def compute (f : σ → σ) (t : thread_state σ τ) : thread_state σ τ :=
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
/-- thread can only be active either in ac₁ or ac₂ -/
def ac_distinct (ac₁ ac₂ : vector bool n) : Prop := ∀ (i : fin n), ac₁.nth i = ff ∨ ac₂.nth i = ff

/-- Global program state -/
structure state {ι : Type} (n : ℕ) (σ : Type) (τ : ι → Type) : Type :=
(threads : vector (thread_state σ τ) n)

namespace state

def map_threads (f : thread_state σ τ → thread_state σ τ) (s : state n σ τ) : state n σ τ :=
{ threads := s.threads.map f, ..s }

-- we generally don't want to unfold this if possible
-- this would for example happen when you do cases in (exec_state (compute f) ...) 
@[irreducible]
def map_active_threads (ac : vector bool n) (f : thread_state σ τ → thread_state σ τ) (s : state n σ τ) : state n σ τ :=
{ threads := (s.threads.map₂ (λ t (a : bool), if a then f t else t) ac), ..s }

def active_threads (ac : vector bool n) (s : state n σ τ) : list (thread_state σ τ) :=
((s.threads.map₂ prod.mk ac).to_list.filter (λ c : (thread_state σ τ × bool), c.2)).map (λ ⟨t, a⟩, t)

-- case 1: no thread changed ι and shadows must be equal at ι
-- case 2: thread t changed ι and all other threads must not access ι
def syncable (s : state n σ τ) (m : memory τ) : Prop :=
∀i:ι,
  (∀ tid, i ∉ (s.threads.nth tid).stores ∧ m i = (s.threads.nth tid).global i) ∨
  (∃ tid, i ∈ (s.threads.nth tid).stores ∧ m i = (s.threads.nth tid).global i ∧
    (∀ tid', tid ≠ tid' → i ∉ (s.threads.nth tid').accesses))

def precedes (s u : state n σ τ) : Prop :=
∀ (t : thread_state σ τ × thread_state σ τ), t ∈ (s.threads.map₂ prod.mk u.threads) → t.1.stores ⊆ t.2.stores ∧ t.1.loads ⊆ t.2.loads

end state

@[irreducible]
def deactivate_threads (f : σ → bool) (ac : vector bool n) (s : state n σ τ) : vector bool n := (ac.map₂ prod.mk s.threads).map (λ ⟨a, t⟩, (bnot ∘ f) t.tlocal && a)

def subkernel (q : kernel σ τ) : kernel σ τ → Prop
| (seq k₁ k₂) := k₁ = q ∨ k₂ = q ∨ subkernel k₁ ∨ subkernel k₂
| (ite c th el) := th = q ∨ el = q ∨ subkernel th ∨ subkernel el
| (loop c body) := body = q ∨ subkernel body
| k := k = q

/-- Execute a kernel on a global state, i.e. a list of threads -/
inductive exec_state {n : ℕ} : kernel σ τ → vector bool n → state n σ τ → state n σ τ → Prop
| load (f) (s : state n σ τ) (ac : vector bool n) :
  exec_state (load f) ac s (s.map_active_threads ac $ thread_state.load f)
| store (f) (s : state n σ τ) (ac : vector bool n) :
  exec_state (store f) ac s (s.map_active_threads ac $ thread_state.store f)
| compute (f : σ → σ) (s : state n σ τ) (ac : vector bool n) :
  exec_state (compute f) ac s (s.map_active_threads ac $ thread_state.compute f)
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

def kernel_transform_func (k) (f) (n) (ac) : Prop := ∀ (s u : state n σ τ), exec_state k ac s u ↔ (u = s.map_active_threads ac f)

def contains_sync : kernel σ τ → Prop
| (sync) := true
| (seq k₁ k₂) := contains_sync k₁ ∨ contains_sync k₂
| (load _) := false
| (store _) := false
| (compute _) := false
| (ite c k₁ k₂) := contains_sync k₁ ∨ contains_sync k₂
| (loop c k) := contains_sync k

inductive program {ι : Type} (σ : Type) (τ : ι → Type)
| intro (f : memory τ → ℕ) (k : kernel σ τ) : program

def state_initializer := ℕ → σ

@[reducible]
def init_state (init : ℕ → σ) (f : memory τ → ℕ) (m : memory τ) : state (f m) σ τ := 
{ threads := (vector.range (f m)).map (λ n, { tlocal := init n, global := m, loads := ∅, stores := ∅ })}

inductive exec_prog : (ℕ → σ) → program σ τ → memory τ → memory τ → Prop
| intro (k : kernel σ τ) (f : memory τ → ℕ) (a b : memory τ) (init : ℕ → σ) (s' : state (f a) σ τ) (hsync : s'.syncable b)
  (he : exec_state k (vector.repeat tt (f a)) (init_state init f a) s') : 
  exec_prog init (program.intro f k) a b

def list_to_kernel_seq (ks : list (kernel σ τ)) : kernel σ τ := ks.foldl (λ k₁ k₂, k₁ ;; k₂) (kernel.compute id)

end parlang