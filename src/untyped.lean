import data.set.basic

namespace MCL_untyped

inductive type
| int
| float

open type

@[reducible]
def type_map : type → Type
| int := ℕ
| float := ℕ

@[reducible]
def untyped_value := ℕ

-- TODO this shouldn't be a function at all
-- that way we don't have to care about types of the values
@[reducible]
def var_map : Type := string → list ℕ → untyped_value

def var_map.update (n : string) (n_idx : list ℕ) (v : untyped_value) (s : var_map) := λm m_idx, if n = m ∧ n_idx = m_idx then v else s m m_idx

structure state := (global : var_map)

inductive expression : Type
| var (n : string) : expression
| add : expression → expression → expression
| literal_int {} (n : ℕ) : expression

instance : has_add expression := ⟨expression.add⟩
instance : has_zero expression := ⟨expression.literal_int 0⟩
instance : has_one expression := ⟨expression.literal_int 1⟩
open expression

inductive valid_int_expression : expression → ℕ → Prop
| var (n : string) : valid_int_expression (var n) 0 -- all variable are 0 at the moment
| add {e₁ e₂ n₁ n₂} (h₁ : valid_int_expression e₁ n₁) (h₂ : valid_int_expression e₂ n₂) : valid_int_expression (add e₁ e₂) (n₁ + n₂)
| literal {n} : valid_int_expression (literal_int n) n

-- def pred_on_list (α : Type) : list α → Prop
-- | (x :: xs) := 

inductive program
| assign (n : string) : list (expression) → expression → program
| seq : program → program → program
| loop (n : string) : expression → program → program
| skip : program

infixr ` ;; `:90 := program.seq
open program

inductive big_step : (program × state) → state → Prop
| assign_global_int {n expr val} {s u : state} {idx_expr : list expression} {idx_evaled : list ℕ} (h_eval : valid_int_expression expr val) 
    -- (h_idx : (idx_expr.zip idx_evaled).all (λ x, valid_int_expression x.1 x.2))
    (h_idx_length : idx_expr.length = idx_evaled.length)
    (h_carryover : ∀ m m_idx, ¬(n = m ∧ idx_evaled = m_idx) → u.global m m_idx = s.global m m_idx)
    (h_updated : u.global n idx_evaled = val) : 
    big_step ((assign n idx_expr expr), s) u
| seq {s u v p₁ p₂} (hp₁ : big_step (p₁, s) u) (hp₂ : big_step (p₂, u) v) :
    big_step (seq p₁ p₂, s) v

infix ` ⟹ `:110 := big_step

def p : program :=
    assign "n" [] (literal_int 0)

theorem x : {string_imp . data := ['n']} = "n" := by refl

example {s u} (hp : (p, s) ⟹ u) : u.global "n" [] = 1 := begin
    cases hp,
    simp * at *,
    have : hp_idx_evaled = [] := begin
        apply list.eq_nil_of_length_eq_zero,
        apply eq.symm,
        assumption
    end,
    rw <- this,
    rw x at hp_h_updated,
    rw hp_h_updated,
    cases hp_h_eval,
end

end MCL_untyped