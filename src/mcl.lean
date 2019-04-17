
import parlang
import rel_hoare
open parlang

namespace mcl
variables {n : ℕ}

inductive type
| int
| float
| bool

open type

inductive scope
| tlocal
| global

structure variable_def :=
(type : type)
(scope : scope)

@[reducible]
def signature := string → variable_def

variables {sig : signature}

@[reducible]
def create_signature : list (string × type) → signature
| [] n := int
| ((m, t) :: xs) n := if m = n then t else create_signature xs n

@[reducible]
def type_map : type → Type
| int := ℕ
| float := ℕ
| bool := bool

def type_of : variable_def → type := λ v, v.type
def lean_type_of : variable_def → Type := λ v, type_map (type_of v)
def signature.type_of (n : string) (sig :signature) := type_of (sig n)
def signature.lean_type_of (n : string) (sig : signature) := lean_type_of (sig n)
def is_tlocal : variable_def → Prop := λ v, v.scope = scope.tlocal
def is_global : variable_def → Prop := λ v, v.scope = scope.global

@[reducible]
def state (sig : signature) : Type := Π n : string, lean_type_of (sig n)

def state.update {sig : signature} (name : string) (val : lean_type_of (sig name)) (s : state sig) : state sig :=
λn, if h : n = name then by rw [h]; exact val else (s n)

def state.update' {sig : signature} {t : type} {name : string} (eq : type_of (sig name) = t) (val : type_map t) (s : state sig) : state sig :=
state.update name (by rw [eq]; exact val) s

def state.get' {sig : signature} {t : type} {name : string} (eq : type_of (sig name) = t) (s : state sig) : type_map t :=
by rw [← eq]; exact s name

inductive expression (sig : signature) : type → Type
| tlocal_var {t} (n : string) (h : type_of (sig n) = t) (h₂ : is_tlocal (sig n)) : expression t
| global_var {t} (n : string) (h : type_of (sig n) = t) (h₂ : is_global (sig n)) : expression t
| add {t} : expression t → expression t → expression t
| const_int {} {t} (n : ℕ) (h : t = type.int) : expression t
| smaller {t} (h : t = type.bool) : expression int → expression int → expression t

open expression

instance (t : type) : has_add (expression sig t) := ⟨expression.add⟩
instance : has_zero (expression sig int) := ⟨expression.const_int 0 rfl⟩
instance : has_one (expression sig int) := ⟨expression.const_int 1 rfl⟩

def type_map_add : Π{t : type}, type_map t → type_map t → type_map t
| int a b := a + b
| float a b := a + b
| bool a b := a ∧ b


def eval {sig : signature} : Π {t : type}, state sig → expression sig t → type_map t
| t s (tlocal_var n h h₂) := (by rw [←h]; exact s n)
| t s (global_var n h h₂) := (by rw[←h]; exact s n) -- requires that the global variable has been loaded into tstate under the same name
| t s (add a b) := type_map_add (eval s a) (eval s b)
| t s (const_int n h) := (by rw [h]; exact n)
| t s (smaller h a b) := (by rw h; exact ((eval s a) < (eval s b)))

def load_global_vars_for_expr {sig : signature} : Π {t : type}, expression sig t → list (kernel (state sig) (λ n, sig.lean_type_of n))
| t (global_var n h _) := [kernel.load (λ s, ⟨n, λ v, s.update' (show type_of (sig n) = type_of (sig n), by refl) v⟩)]
| t (add a b) := load_global_vars_for_expr a ++ load_global_vars_for_expr b
| t (tlocal_var _ _ _) := []
| t (const_int _ _) := []
| t (smaller _ a b) := load_global_vars_for_expr a ++ load_global_vars_for_expr b

def prepend_load_expr {sig : signature} {t : type} (expr : expression sig t) (k : kernel (state sig) (λ n, sig.lean_type_of n)) :=
list_to_kernel_seq (load_global_vars_for_expr expr ++ [k])

-- TODO prove lemma
-- eval expression (specifically the loads only ever )
-- prove more lemmas to make sure loads are placed correctly

notation `v(` n `)`:= expression.tlocal_var n (by refl)
infixr ` ~+ `:90 := expression.add
notation `i(` n `)`:= expression.const_int n (by refl)

open expression

def expr_uses (n : string) : Π {t : type}, expression sig t → Prop
| t (tlocal_var m _ _) := m = n
| t (global_var m _ _) := m = n
| t (add expr₁ expr₂) := expr_uses expr₁ ∨ expr_uses expr₂
| t (const_int _ _) := false
| t (smaller _ a b) := expr_uses a ∨ expr_uses b

inductive mclk (sig : signature)
| tlocal_assign (n : string) : (expression sig (type_of (sig n))) → mclk
| global_assign (n) : (expression sig (type_of (sig n))) → mclk
| seq : mclk → mclk → mclk
| for (n : string) (h : sig.type_of n = int) :
  expression sig int → (state sig → bool) → mclk → mclk → mclk
| skip : mclk

infixr ` ;; `:90 := mclk.seq

open mclk

-- split the signature 
def mclk_to_kernel : mclk sig → kernel (state sig) (λ n, sig.lean_type_of n)
| (seq k₁ k₂) := kernel.seq (mclk_to_kernel k₁) (mclk_to_kernel k₂)
| (skip _) := kernel.compute id
| (tlocal_assign n expr) := prepend_load_expr expr (kernel.compute (λ s : state sig, s.update' (by refl) (eval s expr)))
| (global_assign n expr) := prepend_load_expr expr (kernel.compute (λ s, s.update' (by refl) (eval s expr))) ;; kernel.store (λ s, ⟨n, s.get' (by refl)⟩)
| (for n h expr c k_inc k_body) := prepend_load_expr expr (kernel.compute (λ s, s.update' h (eval s expr))) ;; kernel.loop (λ s, c s) (mclk_to_kernel k_body ;; mclk_to_kernel k_inc)

@[reducible]
def state_assert (sig₁ sig₂ : signature) := Π n₁:ℕ, parlang.state n₁ (state sig₁) (λ n, type_map (sig₁.type_of n)) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (λ n, type_map (sig₂.type_of n)) → vector bool n₂ → Prop

def mclk_rel {sig₁ sig₂ : signature} 
    (P : Π n₁:ℕ, parlang.state n₁ (state sig₁) (λ n, (sig₁.lean_type_of n)) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (λ n, (sig₂.lean_type_of n)) → vector bool n₂ → Prop)
    (k₁ : mclk sig₁) (k₂ : mclk sig₂)
    (Q : Π n₁:ℕ, parlang.state n₁ (state sig₁) (λ n, (sig₁.lean_type_of n)) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (λ n, (sig₂.lean_type_of n)) → vector bool n₂ → Prop) := 
rel_hoare_state P (mclk_to_kernel k₁) (mclk_to_kernel k₂) Q

inductive mclp (sig : signature)
| intro (f : memory (λ n, (sig.lean_type_of n)) → ℕ) (k : mclk sig) : mclp

def mclp_to_program {sig : signature} : mclp sig → parlang.program (state sig) (λ n, type_map (sig n))
| (mclp.intro f k) := parlang.program.intro f (mclk_to_kernel k)

-- we need an assumption on the signature, i.e. tid must be int
def mcl_init {sig : signature} : ℕ → state sig := λ n : ℕ, λ name, if name = "tid" then n else 0

def mclp_rel {sig₁ sig₂ : signature} (P) (p₁ : mclp sig₁) (p₂ : mclp sig₂) (Q) := rel_hoare_program mcl_init mcl_init P (mclp_to_program p₁) (mclp_to_program p₂) Q

--def eq_assert (sig₁ : signature) : state_assert sig₁ sig₁ := λ n₁ s₁ ac₁ n₂ s₂ ac₂, n₁ = n₂ ∧ s₁ = s₂ ∧ ac₁ = ac₂

example (P) (n) (expr) : mclk_rel P (tlocal_assign n expr)

-- we have to show some sort of non-interference
example {sig : signature} {n} {k₁} {P Q : state_assert sig sig} (h : sig "i" = int) (hpi : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → n₁ = n) : mclk_rel P k₁ (for "i" h 0 (λ s, s.get' h < n) (tlocal_assign "i" (var "i" (by refl) + (const_int 1 h))) k₁) Q := begin
    sorry
end

example {t : type} {n : string} {sig₁ sig₂ : signature} {P Q} {expr} {k₂ : mclk sig₂} (hu : ¬expr_uses n expr)
(hr : @mclk_rel sig₁ sig₂ P (tlocal_assign n expr ;; tlocal_assign n expr) k₂ Q) : 
@mclk_rel sig₁ sig₂ P (tlocal_assign n expr) k₂ Q := begin
    unfold mclk_rel,
    rw mclk_to_kernel,
    intros _ _ _ _ _ _ _ hp hek₁,
    specialize hr n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ hp,
    apply hr,
    unfold mclk_to_kernel,
    apply exec_state.seq,
    {
        apply exec_state.compute,
    }, {
        suffices : s₁' = state.map_active_threads ac₁ (thread_state.map (λ (s : state sig₁), state.update' _ (eval expr s) s)) (state.map_active_threads ac₁ (thread_state.map (λ (s : state sig₁), state.update' _ (eval expr s) s)) s₁),
        {
            subst this,
            apply exec_state.compute,
        }, {
            sorry,
        }
    }
end

end mcl