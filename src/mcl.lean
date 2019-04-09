
import parlang
import rel_hoare
open parlang

namespace mcl

inductive type
| int
| float

open type

@[reducible]
def signature := string → type

@[reducible]
def create_signature : list (string × type) → signature
| [] n := int
| ((m, t) :: xs) n := if m = n then t else create_signature xs n

@[reducible]
def type_map : type → Type
| int := ℕ
| float := ℕ

@[reducible]
def state (sig : signature) : Type := Π n : string, type_map (sig n)

def state.update {sig : signature} (name : string) (val : type_map (sig name)) (s : state sig) : state sig :=
λn, if h : n = name then by rw [h]; exact val else (s n)

def state.update' {sig : signature} {t : type} {name : string} (eq : sig name = t) (val : type_map t) (s : state sig) : state sig :=
state.update name (by rw [eq]; exact val) s

def state.get' {sig : signature} {t : type} {name : string} (eq : sig name = t) (s : state sig) : type_map t :=
by rw [← eq]; exact s name

inductive expression (sig : signature) (t : type) : Type
| var (n : string) (h : sig n = t) : expression
| add : expression → expression → expression
| const_int {} (n : ℕ) (h : t = int) : expression

instance (sig : signature) (t : type) : has_add (expression sig t) := ⟨expression.add⟩
instance (sig : signature) : has_zero (expression sig int) := ⟨expression.const_int 0 rfl⟩
instance (sig : signature) : has_one (expression sig int) := ⟨expression.const_int 1 rfl⟩

def eval {sig : signature} {t : type} (expr : expression sig t) (s : state sig) : type_map t := sorry

notation `v(` n `)`:= expression.var n (by refl)
infixr ` ~+ `:90 := expression.add
notation `i(` n `)`:= expression.const_int n (by refl)

open expression

def expr_uses {sig : signature} {t : type} (n : string) : expression sig t → Prop
| (var m _) := m = n
| (add expr₁ expr₂) := expr_uses expr₁ ∨ expr_uses expr₂
| (const_int _ _) := false

inductive mclk (sig : signature)
| tlocal_assign (n : string) : (expression sig (sig n)) → mclk
| global_assign (n) : (expression sig (sig n)) → mclk
| seq : mclk → mclk → mclk
| for (n : string) (h : sig n = int) :
  expression sig int → (state sig → bool) → mclk → mclk → mclk
| skip : mclk

infixr ` ;; `:90 := mclk.seq

open mclk

def mclk_to_kernel {sig : signature} : mclk sig → kernel (state sig) (λ n, type_map (sig n))
| (seq k₁ k₂) := kernel.seq (mclk_to_kernel k₁) (mclk_to_kernel k₂)
| (skip _) := kernel.compute id
| (tlocal_assign n expr) := kernel.compute (λ s, s.update' (by refl) (eval expr s) )
| (global_assign n expr) := kernel.compute (λ s, s.update' (by refl) (eval expr s)) ;; kernel.store (λ s, ⟨n, s.get' (by refl)⟩)
| (for n h expr c k_inc k_body) := kernel.compute (λ s, s.update' h (eval expr)) ;; kernel.loop (λ s, c s) (mclk_to_kernel k_body ;; mclk_to_kernel k_inc)

@[reducible]
def state_assert (sig₁ sig₂ : signature) := Π n₁:ℕ, parlang.state n₁ (state sig₁) (λ n, type_map (sig₁ n)) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (λ n, type_map (sig₂ n)) → vector bool n₂ → Prop

def mclk_rel {sig₁ sig₂ : signature} 
    (P : Π n₁:ℕ, parlang.state n₁ (state sig₁) (λ n, type_map (sig₁ n)) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (λ n, type_map (sig₂ n)) → vector bool n₂ → Prop)
    (k₁ : mclk sig₁) (k₂ : mclk sig₂)
    (Q : Π n₁:ℕ, parlang.state n₁ (state sig₁) (λ n, type_map (sig₁ n)) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (λ n, type_map (sig₂ n)) → vector bool n₂ → Prop) := 
rel_hoare_state P (mclk_to_kernel k₁) (mclk_to_kernel k₂) Q

inductive mclp {sig : signature}
| intro (f : memory (λ n, type_map (sig n)) → ℕ) (k : mclk sig) : mclp

--def eq_assert (sig₁ : signature) : state_assert sig₁ sig₁ := λ n₁ s₁ ac₁ n₂ s₂ ac₂, n₁ = n₂ ∧ s₁ = s₂ ∧ ac₁ = ac₂

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