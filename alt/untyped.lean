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

prefix ▸ := type_map

@[reducible]
def untyped_value := ℕ

@[reducible]
def var_map : Type := Π t : type, string → list ℕ → ▸t

def var_map.update (t : type) (n : string) (n_idx : list ℕ) (v : ▸t) (s : var_map) := 
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


structure declaration := (scope : ℕ)(type : type)(nridx : ℕ)
def signature := string → option declaration

inductive expression : Type
| var (n : string) (idx : list expression) : expression
| add : expression → expression → expression
| literal_int {} (n : ℕ) : expression

instance : has_add expression := ⟨expression.add⟩
instance : has_zero expression := ⟨expression.literal_int 0⟩
instance : has_one expression := ⟨expression.literal_int 1⟩
open expression

inductive compute_typed_expression (sig : signature) (s : state) : Π t : type, expression → ▸t → Prop
| global_var (n : string) (d) {t : type} {idx_expr idx_evaled} (hs : sig n = some d) (ht : t = d.type) (hi : list.forall₂ (compute_typed_expression int) idx_expr idx_evaled) : 
    compute_typed_expression t (var n idx_expr) (s.global t n idx_evaled) -- equality as hypthoses allows to to call cases on h₂ in compute_typed_expression_unique
| add {e₁ e₂ n₁ n₂} (h₁ : compute_typed_expression int e₁ n₁) (h₂ : compute_typed_expression int e₂ n₂) : compute_typed_expression int (add e₁ e₂) (n₁ + n₂)
| literal {n} : compute_typed_expression int (literal_int n) n

#check compute_typed_expression.literal 

@[simp] -- causes the empty list to be simplified immediately (no unfold required)
def compute_expr_list (t sig s) (idx_expr : list expression) (idx_evaled : list (▸t)) := list.forall₂ (λ expr eval, compute_typed_expression sig s t expr eval) idx_expr idx_evaled

@[simp]
def compute_idx_expr := compute_expr_list int

inductive program
| assign (n : string) : list (expression) → expression → program
| seq : program → program → program
| loop (n : string) : expression → program → program
| skip : program

infixr ` ;; `:90 := program.seq
open program

inductive big_step : (program × signature × state) → state → Prop
| assign_global {t : type} {n expr d} {sig : signature} {val} {s : state} {idx_expr : list expression} {idx_evaled : list ℕ} 
    (ht : sig n = some d) 
    (h_eval : compute_typed_expression sig s d.type expr val) 
    (h_idx : compute_idx_expr sig s idx_expr idx_evaled) :
    big_step ((assign n idx_expr expr), sig, s) { global := s.global.update d.type n idx_evaled val , ..s }
| seq {s u v sig p₁ p₂} (hp₁ : big_step (p₁, sig, s) u) (hp₂ : big_step (p₂, sig, u) v) :
    big_step (seq p₁ p₂, sig, s) v

infix ` ⟹ `:110 := big_step

lemma compute_typed_expression_unique {sig s t expr r₁ r₂} (h₂ : compute_typed_expression sig s t expr r₂) (h₁ : compute_typed_expression sig s t expr r₁) :
    r₁ = r₂ := begin
    induction h₁,
    {
        cases h₂,
        have : h₁_idx_evaled = h₁_idx_evaled := begin
            have : relator.right_unique (compute_typed_expression sig s int) := begin
                unfold relator.right_unique,
                intros expr val₁ val₂ h₁ h₂,
                -- PROBLEM: i don't get IH for (list.forall₂ (compute_typed_expression)) because the recursor does not support it
                sorry
            end,
            sorry,
            --apply list.right_unique_forall₂,
        end,
        sorry,
        -- refl,
    },
    {
        cases h₂,
        have : h₁_n₁ = h₂_n₁ := by apply h₁_x h₂_h₁,
        rw this,
        have : h₁_n₂ = h₂_n₂ := by apply h₁_x_1 h₂_h₂,
        rw this,
        refl,
    }, {
        cases h₂,
        refl,
    }
end

lemma compute_typed_expression_right_unique {sig s t} : relator.right_unique (compute_typed_expression sig s t) := begin
    unfold relator.right_unique,
    intros expr val₁ val₂ h₁ h₂,
    apply compute_typed_expression_unique,
    repeat { assumption },
end

lemma compute_expr_list_unique {sig s} {t : type} {idx_expr : list expression}  {eval₁ eval₂} 
    (h₁ : compute_expr_list t sig s idx_expr eval₁) (h₂ : compute_expr_list t sig s idx_expr eval₂) : eval₁ = eval₂ := 
begin
    -- rw ← list.forall₂_eq_eq_eq, -- does rewrite perform funext here?
    apply list.right_unique_forall₂ (@compute_typed_expression_right_unique sig s t),
    repeat { assumption },
end

@[simp]
lemma big_step_assign {sig s u expr n idx_expr idx_evaled} {d : declaration} {val : ▸(d.type)}
    (hp : ((assign n idx_expr expr), sig, s) ⟹ u) (hi : compute_idx_expr sig s idx_expr idx_evaled) 
    (hd : sig n = some d) (he : compute_typed_expression sig s (d.type) expr val) : 
    s.global.update (d.type) n idx_evaled val = u.global := 
begin
    cases hp,
    simp,
    have : hp_idx_evaled = idx_evaled := by apply compute_expr_list_unique hp_h_idx hi,
    subst this,
    rw hd at hp_ht,
    simp at hp_ht,
    subst hp_ht,
    have : val = hp_val := by apply compute_typed_expression_unique he hp_h_eval,
    subst this,
end

lemma big_step_assign' {sig s u expr n idx_expr}
    (hp : ((assign n idx_expr expr), sig, s) ⟹ u) :
    ∃ (d : declaration) idx_evaled val, s.global.update (d.type) n idx_evaled val = u.global := begin
    cases hp,
    apply Exists.intro hp_d,
    apply Exists.intro hp_idx_evaled,
    apply Exists.intro hp_val,
    simp,
end

-- lemma big_step_seq {s} () : := begin

def s₁ : signature
| "n" := some {scope := 1, type := int, nridx := 0}
| _ := none

def p : program :=
    assign "n" [] (literal_int 1)

set_option trace.simplify.rewrite true 

example {s u} (hp : (p, s₁, s) ⟹ u) : u.global int "n" [] = 1 := begin
    cases hp,
    simp at hp_ht,
    cases hp_ht,
    simp,
    cases hp_h_eval,
    sorry,
    -- apply var_map_update_get,
    -- simp,
end

end MCL_untyped