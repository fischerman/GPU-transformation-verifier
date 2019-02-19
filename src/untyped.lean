import data.set.basic
import data.list
import logic.relator

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

@[simp]
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

inductive compute_typed_expression (s : state) : Π t : type, expression → type_map t → Prop
| global_var (n : string) (t : type) : compute_typed_expression t (var n) (s.global t n []) -- variables can have arbitrary values
| add {e₁ e₂ n₁ n₂} (h₁ : compute_typed_expression int e₁ n₁) (h₂ : compute_typed_expression int e₂ n₂) : compute_typed_expression int (add e₁ e₂) (n₁ + n₂)
| literal {n} : compute_typed_expression int (literal_int n) n

inductive program
| assign (n : string) : list (expression) → expression → program
| seq : program → program → program
| loop (n : string) : expression → program → program
| skip : program

infixr ` ;; `:90 := program.seq
open program

@[simp] -- causes the empty list to be simplified immediately (no unfold required)
def compute_expr_list (t s) (idx_expr : list expression) (idx_evaled : list (type_map t)) := list.forall₂ (λ expr eval, compute_typed_expression s t expr eval) idx_expr idx_evaled

@[simp]
def compute_idx_expr := compute_expr_list int

inductive big_step : (program × state) → state → Prop
| assign_global {t : type} {n expr} {val : type_map t} {s : state} {idx_expr : list expression} {idx_evaled : list ℕ} (h_eval : compute_typed_expression s t expr val) 
    (h_idx : compute_idx_expr s idx_expr idx_evaled) : 
    big_step ((assign n idx_expr expr), s) { global := s.global.update t n idx_evaled val , ..s }
| seq {s u v p₁ p₂} (hp₁ : big_step (p₁, s) u) (hp₂ : big_step (p₂, u) v) :
    big_step (seq p₁ p₂, s) v

infix ` ⟹ `:110 := big_step

lemma compute_typed_expression_unique {s t expr r₁ r₂} (h₁ : compute_typed_expression s expr t r₁) (h₂ : compute_typed_expression s expr t r₂) : r₁ = r₂ := begin
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

lemma compute_typed_expression_right_unique {s t} : relator.right_unique (compute_typed_expression s t) := begin
    unfold relator.right_unique,
    intros expr val₁ val₂ h₁ h₂,
    apply compute_typed_expression_unique,
    repeat { assumption },
end

lemma compute_expr_list_unique {s} {t : type} {idx_expr : list expression}  {eval₁ eval₂} 
    (h₁ : compute_expr_list t s idx_expr eval₁) (h₂ : compute_expr_list t s idx_expr eval₂) : eval₁ = eval₂ := 
begin
    -- rw ← list.forall₂_eq_eq_eq, -- does rewrite perform funext here?
    apply list.right_unique_forall₂ (@compute_typed_expression_right_unique s t),
    repeat { assumption },
end

-- could be changed to equality of the state
@[simp]
lemma big_step_assign_int {s u val n idx_expr idx_evaled} (hp : ((assign n idx_expr (literal_int val)), s) ⟹ u) (hi : compute_idx_expr s idx_expr idx_evaled) : 
    u.global int n idx_evaled = val := 
begin
    cases hp,
    have : hp_idx_evaled = idx_evaled := begin
        apply compute_expr_list_unique hp_h_idx hi,
    end,
    rw <- this,
    cases hp_h_eval,
    simp,
end

@[simp]
lemma big_step_assign {s u t expr val n idx_expr idx_evaled} 
    (hp : ((assign n idx_expr expr), s) ⟹ u) (hi : compute_idx_expr s idx_expr idx_evaled) (he : compute_typed_expression s t expr val) : 
    s.global.update t n idx_evaled val = u.global := 
begin
    cases hp,
    simp,
    have : hp_idx_evaled = idx_evaled := begin
        apply compute_expr_list_unique hp_h_idx hi,
    end,
    subst this,
    -- it cannot be proven, because assign can assume an type
    cases hp_h_eval,
end

-- lemma big_step_seq {s} () : := begin

def p : program :=
    assign "n" [] (literal_int 1)

example {s u} (hp : (p, s) ⟹ u) : u.global int "n" [] = 1 := begin
    apply big_step_assign_int,
    assumption,
    simp,
end

end MCL_untyped