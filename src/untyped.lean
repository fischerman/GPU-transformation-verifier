import data.set.basic
import data.list

#check list.forall₂

namespace MCL_untyped

inductive type
| int
| float

open type

instance : decidable_eq type := sorry

@[reducible]
def type_map : type → Type
| int := ℕ
| float := ℕ

@[reducible]
def untyped_value := ℕ

@[reducible]
def var_map : Type := Π t : type, string → list ℕ → type_map t

def var_map.update (t : type) (n : string) (n_idx : list ℕ) (v : type_map t) (s : var_map) := 
    λ t' m m_idx, if c : (n = m ∧ n_idx = m_idx ∧ t = t') then (begin
        rw [and.right (and.right c)] at v,
        exact v,
    end) else s t' m m_idx

lemma var_map_update_get {t n idx v} {a : var_map} : a.update t n idx v t n idx = v := begin
    unfold var_map.update,
    simp,
    refl,
end

structure state := (global : var_map)
def state.updateGloabl (g : var_map) (s : state) : state := {global := g, ..s}

inductive expression : Type
| var (n : string) : expression
| add : expression → expression → expression
| literal_int {} (n : ℕ) : expression

instance : has_add expression := ⟨expression.add⟩
instance : has_zero expression := ⟨expression.literal_int 0⟩
instance : has_one expression := ⟨expression.literal_int 1⟩
open expression

inductive valid_typed_expression (s : state) : expression → Π t : type, type_map t → Prop
| global_var (n : string) (t : type) : valid_typed_expression (var n) t (s.global t n []) -- variables can have arbitrary values
| add {e₁ e₂ n₁ n₂} (h₁ : valid_typed_expression e₁ int n₁) (h₂ : valid_typed_expression e₂ int n₂) : valid_typed_expression (add e₁ e₂) int (n₁ + n₂)
| literal {n} : valid_typed_expression (literal_int n) int n

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
def int_expression_list_eval (s) (idx_expr : list expression) (idx_evaled : list ℕ) := 
    pred_on_list (λ x : (expression × ℕ), valid_typed_expression s x.1 int x.2) (idx_expr.zip idx_evaled) ∧
    idx_expr.length = idx_evaled.length

@[simp]
lemma int_expression_list_eval_empty (s) : int_expression_list_eval s [] [] := begin
    unfold int_expression_list_eval,
    simp,
end

inductive big_step : (program × state) → state → Prop
| assign_global {t : type} {n expr} {val : type_map t} {s : state} {idx_expr : list expression} {idx_evaled : list ℕ} (h_eval : valid_typed_expression s expr t val) 
    (h_idx : int_expression_list_eval s idx_expr idx_evaled) : 
    big_step ((assign n idx_expr expr), s) { global := s.global.update t n idx_evaled val , ..s }
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
    assumption,
end

lemma valid_typed_expression_unique {s t expr r₁ r₂} (h₁ : valid_typed_expression s expr t r₁) (h₂ : valid_typed_expression s expr t r₂) : r₁ = r₂ := begin
    induction h₁;
        cases h₂;
        try {refl},
    {
        have : h₁_n₁ = h₂_n₁ := by apply h₁_ih_h₁ h₂_h₁,
        rw this,
        have : h₁_n₂ = h₂_n₂ := by apply h₁_ih_h₂ h₂_h₂,
        rw this,
        refl,
    }
end

theorem int_expression_list_unique {s expr eval₁ eval₂} (h₁ : int_expression_list_eval s expr eval₁) (h₂ : int_expression_list_eval s expr eval₂) : eval₁ = eval₂ := begin
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
            have hd_eq₁ : valid_typed_expression s expr_hd int eval₁_hd := begin
                rw list.zip at h₁_left,
                rw list.zip_with at h₁_left,
                apply pred_on_list_head h₁_left,
            end,
            have hd_eq₂ : valid_typed_expression s expr_hd int eval₂_hd := begin
                rw list.zip at h₂_left,
                rw list.zip_with at h₂_left,
                apply pred_on_list_head h₂_left,
            end,
            apply valid_typed_expression_unique hd_eq₁ hd_eq₂,
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

-- could be changed to equality of the state
@[simp]
lemma big_step_assign {s u val n idx_expr idx_evaled} (hp : ((assign n idx_expr (literal_int val)), s) ⟹ u) (hi : int_expression_list_eval s idx_expr idx_evaled) : 
    u.global int n idx_evaled = val := 
begin
    cases hp,
    have : hp_idx_evaled = idx_evaled := begin
        apply int_expression_list_unique hp_h_idx hi,
    end,
    rw <- this,
    cases hp_h_eval,
    simp,
    apply var_map_update_get,
end

@[simp]
lemma big_step_assign' {s u val n idx_expr idx_evaled} (hp : ((assign n idx_expr (literal_int val)), s) ⟹ u) (hi : int_expression_list_eval s idx_expr idx_evaled) : 
    s.global.update int n idx_evaled val = u.global := 
begin
    cases hp,
    have : hp_idx_evaled = idx_evaled := begin
        apply int_expression_list_unique hp_h_idx hi,
    end,
    rw <- this,
    cases hp_h_eval,
    simp,
end

-- lemma big_step_seq {s} () : := begin

def p : program :=
    assign "n" [] (literal_int 1)

example {s u} (hp : (p, s) ⟹ u) : u.global int "n" [] = 1 := begin
    apply big_step_assign,
    assumption,
    simp,
end

end MCL_untyped