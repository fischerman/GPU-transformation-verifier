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

inductive program
| assign (n : string) : list (expression) → expression → program
| seq : program → program → program
| loop (n : string) : expression → program → program
| skip : program

infixr ` ;; `:90 := program.seq
open program

def pred_on_list {α : Type} (f : α → Prop) : list α → Prop
| (x :: xs) := f x ∧ pred_on_list xs
| [] := true

@[reducible]
def int_expression_list_eval (idx_expr : list expression) (idx_evaled : list ℕ) := 
    pred_on_list (λ x : (expression × ℕ), valid_int_expression x.1 x.2) (idx_expr.zip idx_evaled) ∧
    idx_expr.length = idx_evaled.length

inductive big_step : (program × state) → state → Prop
| assign_global_int {n expr val} {s u : state} {idx_expr : list expression} {idx_evaled : list ℕ} (h_eval : valid_int_expression expr val) 
    (h_idx : int_expression_list_eval idx_expr idx_evaled)
    (h_carryover : ∀ m m_idx, ¬(n = m ∧ idx_evaled = m_idx) → u.global m m_idx = s.global m m_idx)
    (h_updated : u.global n idx_evaled = val) : 
    big_step ((assign n idx_expr expr), s) u
| seq {s u v p₁ p₂} (hp₁ : big_step (p₁, s) u) (hp₂ : big_step (p₂, u) v) :
    big_step (seq p₁ p₂, s) v

infix ` ⟹ `:110 := big_step

lemma pred_on_list_head {α : Type} {xs : list α} {f x} (hp : pred_on_list f (x :: xs)) : f x := begin
    rw pred_on_list at hp,
    cases hp, 
    assumption,
end

lemma pred_on_list_tail {α : Type} {xs : list α} {f x} (hp : pred_on_list f (x :: xs)) : pred_on_list f xs := begin
    rw pred_on_list at hp,
    cases hp, 
    assumption,
end

lemma list_length_neq_zero {α} {l : list α} (h : ¬(l.length = 0)) : ∃ x xs, l = (x :: xs) := begin
    cases l,
    case list.nil {
        simp at h,
        contradiction
    },
    case list.cons {
        apply Exists.intro l_hd,
        apply Exists.intro l_tl,
        refl,
    }
end

lemma list_length_tail {α β : Type} {x : α} {y : β} {xs ys} (h : (x :: xs).length = (y :: ys).length) : xs.length = ys.length := begin
    rw list.length at h,
    rw list.length at h,
    simp at h,
    repeat { rw nat.one_add at h },
    simp at h,
    assumption,
end

lemma valid_int_expression_eq {expr r₁ r₂} (h₁ : valid_int_expression expr r₁) (h₂ : valid_int_expression expr r₂) : r₁ = r₂ := begin
    cases h₁;
        cases h₂;
        try {refl},
    sorry
end

theorem int_expression_list_unique {expr eval₁ eval₂} (h₁ : int_expression_list_eval expr eval₁) (h₂ : int_expression_list_eval expr eval₂) : eval₁ = eval₂ := begin
    cases h₁,
    cases h₂,
    induction eval₁ generalizing eval₂ expr, -- can pick any list (generalizing the others)
    case list.nil {
        rw h₁_right at h₂_right,
        simp at h₂_right,
        apply eq.symm,
        apply list.eq_nil_of_length_eq_zero,
        apply eq.symm,
        assumption,
    },
    case list.cons {
        -- break out head form eval₂
        have : ∃ x xs, eval₂ = (x :: xs) := begin
            apply list_length_neq_zero,
            rw ← h₂_right,
            rw h₁_right,
            trivial,
        end,
        cases this with eval₂_hd,
        cases this_h with eval₂_tl eval₂_eq,
        subst eval₂_eq,
        -- break out head from expr
        have : ∃ x xs, expr = (x :: xs) := begin
            apply list_length_neq_zero,
            rw h₁_right,
            trivial,
        end,
        cases this with expr_hd,
        cases this_h with expr_tl expr_eq,
        subst expr_eq,
        have : eval₁_hd = eval₂_hd := begin
            have : valid_int_expression expr_hd eval₁_hd := begin
                rw list.zip at h₁_left,
                rw list.zip_with at h₁_left,
                apply pred_on_list_head h₁_left,
            end,
            have : valid_int_expression expr_hd eval₂_hd := begin
                rw list.zip at h₂_left,
                rw list.zip_with at h₂_left,
                apply pred_on_list_head h₂_left,
            end,
            apply valid_int_expression_eq,
            repeat { assumption },
        end,
        cases this,
        have : eval₁_tl = eval₂_tl := begin
            apply (@eval₁_ih eval₂_tl expr_tl),
            {
                apply pred_on_list_tail h₁_left,
            }, {
                apply list_length_tail h₁_right,
            }, {
                apply pred_on_list_tail h₂_left,
            }, {
                apply list_length_tail h₂_right,
            }
        end,
        cases this,
        refl,
    }
end

@[simp]
lemma big_step_assign {s u val n idx_expr idx_evaled} (hp : ((assign n idx_expr (literal_int val)), s) ⟹ u) (hi : int_expression_list_eval idx_expr idx_evaled) : 
    u.global n idx_evaled = val := 
begin
    cases hp,
    have : hp_idx_evaled = idx_evaled := begin
        apply int_expression_list_unique hp_h_idx hi,
    end,
    rw <- this,
    rw hp_h_updated,
    cases hp_h_eval,
    refl,
end

def p : program :=
    assign "n" [] (literal_int 1)

example {s u} (hp : (p, s) ⟹ u) : u.global "n" [] = 1 := begin
    apply big_step_assign,
    assumption,
    
end

end MCL_untyped