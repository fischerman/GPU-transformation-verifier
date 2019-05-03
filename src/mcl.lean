
import parlang
import rel_hoare
open parlang

notation `[` v:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := v

namespace mcl
variables {n : ℕ}

inductive type
| int
| float
| bool

open type

structure array :=
(dim : ℕ)
(sizes : vector ℕ dim)
(type : type)

inductive scope
| tlocal
| global

structure variable_def :=
(type : array)
(scope : scope)

@[reducible]
def signature := string → variable_def

-- todo: make sig parameter (instead of variable). That way I don't have to mention signature anywhere (see section 6.2)
variables {sig : signature}

@[reducible]
def create_signature : list (string × variable_def) → signature
| [] n := { scope := scope.tlocal, type := ⟨1, 1 :: vector.nil, int⟩} -- by default all variables are tlocal int's
| ((m, v) :: xs) n := if m = n then v else create_signature xs n

@[reducible]
def type_map : type → Type
| int := ℕ
| float := ℕ
| bool := _root_.bool

instance (t) : inhabited (type_map t) := ⟨
    match t with 
    | type.int := 0
    | type.float := 0
    | type.bool := ff
    end
⟩

#eval default (type_map int)

@[reducible]
def type_of : variable_def → type := λ v, v.type.type
@[reducible]
def lean_type_of : variable_def → Type := λ v, type_map (type_of v)
@[reducible]
def signature.type_of (n : string) (sig :signature) := type_of (sig n)
@[reducible]
def signature.lean_type_of (n : string) (sig : signature) := lean_type_of (sig n)
@[reducible]
def is_tlocal (v : variable_def) := v.scope = scope.tlocal
@[reducible]
def is_global : variable_def → Prop := λ v, v.scope = scope.global

@[reducible]
def state (sig : signature) : Type := Π (n : string) (idx : vector ℕ (sig n).type.dim), lean_type_of (sig n)

-- type safety is proven given an instance of MCLK (mostly by refl)
-- same is done for the number of array indices
-- the same cannot be done for array indices values (we would have to reason about programs)
-- no out of bound checking
def state.update {sig : signature} (name : string) (idx : vector ℕ (sig name).type.dim) (val : lean_type_of (sig name)) (s : state sig) : state sig :=
λn idxq, if h : n = name 
then by 
    subst h; 
    exact (
        if idx = idxq
        then  val 
        else (s n idxq))
else (s n idxq)

-- update' only requires proofs
-- we once define the structure of the proofs and use them everywhere (as a substitute for the identifier)
-- when we define a program must proofs will be refl
def state.update' {sig : signature} {t : type} {name : string} {dim : ℕ} {idx : vector ℕ dim} (eq : type_of (sig name) = t) (h : (sig name).type.dim = idx.length) (val : type_map t) (s : state sig) : state sig :=
state.update name (by rw [h]; exact idx) (begin unfold lean_type_of, rw [eq], exact val end) s

def state.get' {sig : signature} {t : type} {name : string} {dim : ℕ} {idx : vector ℕ dim} (eq : type_of (sig name) = t) (h : (sig name).type.dim = idx.length) (s : state sig) : type_map t :=
by rw [← eq]; rw [vector.length] at h; rw [← h] at idx; exact s name idx

-- expression is an inductive family over types
-- type is called an index
inductive expression (sig : signature) : type → Type
| tlocal_var {t} {dim : ℕ} (n : string) (idx : fin dim → (expression int)) (h₁ : type_of (sig n) = t) (h₂ : (sig n).type.dim = dim) (h₃ : is_tlocal (sig n)) : expression t
| global_var {t} {dim : ℕ} (n : string) (idx : fin dim → (expression int)) (h₁ : type_of (sig n) = t) (h₂ : (sig n).type.dim = dim) (h₃ : is_global (sig n)) : expression t
| add {t} : expression t → expression t → expression t
| const_int {} {t} (n : ℕ) (h : t = type.int) : expression t
| lt {t} (h : t = type.bool) : expression int → expression int → expression t

open expression

instance (t : type) : has_add (expression sig t) := ⟨expression.add⟩
instance : has_zero (expression sig int) := ⟨expression.const_int 0 rfl⟩
instance : has_one (expression sig int) := ⟨expression.const_int 1 rfl⟩
infix < := expression.lt (show type.bool = type.bool, by refl)
notation `v(` n `)`:= expression.tlocal_var n (by refl)
notation `i(` n `)`:= expression.const_int n (by refl)

def type_map_add : Π{t : type}, type_map t → type_map t → type_map t
| int a b := a + b
| float a b := a + b
| bool a b := a ∧ b

#reduce type.sizeof bool
#reduce type.sizeof int
#check type.no_confusion_type

#reduce expression.sizeof (λ_, { scope := scope.tlocal, type := ⟨_, [1], type.int⟩}) int (add (const_int 4 (by refl)) (const_int 5 (by refl)))
#print expression.sizeof

#check @well_founded.fix

-- idea: convert expression to something untyped, i.e. stripping t
def subterm (q : Σ t : type, expression sig t) : (Σ t : type, expression sig t) → Prop
| ⟨t, add a b⟩ := subterm ⟨t, a⟩ ∨ subterm ⟨t, b⟩
| ⟨t, lt _ a b⟩ := subterm ⟨int, a⟩ ∨ subterm ⟨int, b⟩
| t := t = q

example {sig : signature} : well_founded (@subterm sig) := begin
    apply well_founded.intro,
    sorry,
end

#print expression.sizeof

@[reducible, simp] 
def expression_size {sig : signature} : Π {t : type}, expression sig t → ℕ
| t (const_int _ _) := 1
| t (tlocal_var _ _ _ _ _) := 1
| t (global_var _ _ _ _ _) := 1
| t (add a b) := 
    have a.sizeof sig t < (add a b).sizeof sig t := begin
        rw expression.sizeof,
        simp,
        sorry,
    end,
    have b.sizeof sig t < (add a b).sizeof sig t := sorry,
    expression_size a + expression_size b
| t (lt h a b) := 
    have a.sizeof sig int < (lt h a b).sizeof sig t := sorry,
    have b.sizeof sig int < (lt h a b).sizeof sig t := sorry,
    expression_size a + expression_size b
using_well_founded {rel_tac := λ_ _, `[exact ⟨_, measure_wf (λ ⟨t, e⟩, expression.sizeof sig t e)⟩]}

@[simp]
lemma abc (t) (expr : expression sig t) : 0 < expression_size expr := sorry

-- should we make this an inductive predicate
-- it would have implications on parlang
def eval {sig : signature} (s : state sig) : Π {t : type}, expression sig t → type_map t
| t (tlocal_var n idx h h₂ h₃) := s.get' h (show (sig n).type.dim = ((vector.of_fn idx).map eval).length, from h₂)
| t (global_var n idx h h₂ h₃) := s.get' h (show (sig n).type.dim = ((vector.of_fn idx).map eval).length, from h₂) -- requires that the global variable has been loaded into tstate under the same name
| t (add a b) := type_map_add (eval a) (eval b)
| t (const_int n h) := (by rw [h]; exact n)
| t (lt h a b) := (by rw h; exact ((eval a) < (eval b)))
-- using_well_founded {rel_tac := λ_ _, `[exact ⟨_, measure_wf (λ args : psum (Σ' {t : type}, expression sig t) (list (expression sig int)), match args with
--     | (psum.inl ⟨t, expr⟩) := expression_size expr
--     | (psum.inr exprs) := exprs.length
--     end)⟩], 
-- /- dec_tac := do tactic.interactive.simp -/ }


-- if we compare two variable accesses to the same array: when using vectors we only have to reason about equality of elements, otherwise we have to reason about length as well
@[reducible]
def parlang_mcl_global (sig : signature) := (λ i : string × (list ℕ), sig.lean_type_of i.1)
@[reducible]
def parlang_mcl_kernel (sig : signature) := kernel (state sig) (parlang_mcl_global sig)

def load_global_vars_for_expr {sig : signature} : Π {t : type}, expression sig t → list (parlang_mcl_kernel sig)
| t (global_var n idx h₁ h₂ _) := [kernel.load (λ s, ⟨(n, ((vector.of_fn idx).map (eval s)).to_list), λ v, s.update' (show type_of (sig n) = type_of (sig n), by refl) (show (sig n).type.dim = ((vector.of_fn idx).map (eval s)).length, from h₂) v⟩)]
| t (add a b) := load_global_vars_for_expr a ++ load_global_vars_for_expr b
| t (tlocal_var _ _ _ _ _) := []
| t (const_int _ _) := []
| t (lt _ a b) := load_global_vars_for_expr a ++ load_global_vars_for_expr b

def prepend_load_expr {sig : signature} {t : type} (expr : expression sig t) (k : parlang_mcl_kernel sig) :=
(load_global_vars_for_expr expr).foldr (λ k₁ k₂, k₁ ;; k₂) k
--list_to_kernel_seq (load_global_vars_for_expr expr ++ [k])

def append_load_expr  {sig : signature} {t : type} (expr : expression sig t) (k : parlang_mcl_kernel sig) :=
(load_global_vars_for_expr expr).foldl (λ k₁ k₂, k₁ ;; k₂) k
--list_to_kernel_seq ([k] ++ load_global_vars_for_expr expr)

example (k) : prepend_load_expr (7 : expression sig int) k = k := by refl
example (k) (n idx h₁ h₂ h₃) : prepend_load_expr (@global_var sig _ 1 n idx h₁ h₂ h₃ : expression sig int) k = k := begin
    rw prepend_load_expr,
    rw load_global_vars_for_expr,
    repeat { rw list.foldr },
    sorry
end

example (k) : append_load_expr (7 : expression sig int) k = k := by refl
example (k) (n idx h₁ h₂ h₃) : append_load_expr (@global_var sig _ 1 n idx h₁ h₂ h₃ : expression sig int) k = k := begin
    rw append_load_expr,
    rw load_global_vars_for_expr,
    repeat { rw list.foldl },
    sorry
end

-- TODO prove lemma
-- eval expression (specifically the loads only influence the expression)
-- prove more lemmas to make sure loads are placed correctly
-- do I need a small step seantic for this?

def expr_reads (n : string) : Π {t : type}, expression sig t → Prop
| t (tlocal_var m _ _ _ _) := m = n
| t (global_var m _ _ _ _) := m = n
| t (add expr₁ expr₂) := expr_reads expr₁ ∨ expr_reads expr₂
| t (const_int _ _) := false
| t (lt _ a b) := expr_reads a ∨ expr_reads b

inductive mclk (sig : signature)
| tlocal_assign {dim : ℕ} (n : string) (idx : vector (expression sig int) dim) (h : (sig n).type.dim = idx.length) : (expression sig (type_of (sig n))) → mclk
| global_assign {dim : ℕ} (n) (idx : vector (expression sig int) dim) (h : (sig n).type.dim = idx.length) : (expression sig (type_of (sig n))) → mclk
| seq : mclk → mclk → mclk
| for (n : string) (h : sig.type_of n = int) (h₂ : (sig n).type.dim = 1) :
  expression sig int → expression sig bool → mclk → mclk → mclk
| skip {} : mclk

infixr ` ;; `:90 := mclk.seq

open mclk

def mclk_reads (n : string) : mclk sig → Prop
| (tlocal_assign _ idx _ expr) := expr_reads n expr -- todo add idx in usages
| (global_assign _ idx _ expr) := expr_reads n expr
| (seq k₁ k₂) := mclk_reads k₁ ∨ mclk_reads k₂
| (for _ _ _ init c inc body) := expr_reads n init ∨ expr_reads n c ∨ mclk_reads inc ∨ mclk_reads body
| (skip) := false

--lemma mclk_expr_reads (k) : mclk_reads n k → ∃ expr, (expr_reads n expr ∧ subexpr expr k)

def mclk_to_kernel {sig : signature} : mclk sig → parlang_mcl_kernel sig
| (seq k₁ k₂) := kernel.seq (mclk_to_kernel k₁) (mclk_to_kernel k₂)
| (skip) := kernel.compute id
| (tlocal_assign n idx h expr) := prepend_load_expr expr (kernel.compute (λ s : state sig, s.update' (show type_of (sig n) = type_of (sig n), by refl) (show (sig n).type.dim = (idx.map (eval s)).length, from h) (eval s expr)))
| (global_assign n idx h expr) := prepend_load_expr expr (kernel.compute (λ s, s.update' (show type_of (sig n) = type_of (sig n), by refl) (show (sig n).type.dim = (idx.map (eval s)).length, from h) (eval s expr))) ;; kernel.store (λ s, ⟨(n, (idx.map (eval s)).to_list), s.get' (show type_of (sig n) = type_of (sig n), by refl) (show (sig n).type.dim = (idx.map (eval s)).length, from h)⟩)
| (for n h h₂ expr c k_inc k_body) := prepend_load_expr expr (kernel.compute (λ s, s.update' h (show (sig n).type.dim = (([0] : vector (expression sig int) _).map (eval s)).length, from h₂) (eval s expr))) ;; 
    prepend_load_expr c (
        kernel.loop (λ s, eval s c) (mclk_to_kernel k_body ;; append_load_expr c (mclk_to_kernel k_inc))
    )

-- if a kernel does not contain a global referencce it must not contain any loads
example (k : mclk sig) (h : ∀ n, is_global (sig n) → ¬mclk_reads n k) : ∀ sk, subkernel sk (mclk_to_kernel k) → ¬∃ f, sk = (kernel.load f) := begin
    intros sk hsk hl,
    cases hl with f hl,
    subst hl,
    induction k,
    {
        rw mclk_to_kernel at hsk,
        sorry,
    }, {
        rw mclk_to_kernel at hsk,
        sorry,
    }, {
        rw mclk_to_kernel at hsk,
        rw subkernel at hsk,
        cases hsk,
        {
            sorry, -- trivial but cumbersome
        }, {
            cases hsk,
            {
                sorry,
            }, {
                cases hsk,
                {
                    apply k_ih_a,
                    {
                        intros n hg hr,
                        apply h n hg,
                        left,
                        exact hr,
                    }, {
                        assumption,
                    }
                }, {
                    apply k_ih_a_1,
                    {
                        intros n hg hr,
                        apply h n hg,
                        right,
                        exact hr,
                    }, {
                        assumption,
                    }
                }
            }
        }
    }, {
        sorry,
    }, {
        unfold mclk_to_kernel at hsk,
        rw subkernel at hsk,
        contradiction,
    }
end

@[reducible]
def state_assert (sig₁ sig₂ : signature) := Π n₁:ℕ, parlang.state n₁ (state sig₁) (λ n, type_map (sig₁.type_of n)) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (λ n, type_map (sig₂.type_of n)) → vector bool n₂ → Prop

def mclk_rel {sig₁ sig₂ : signature} 
    (P : Π n₁:ℕ, parlang.state n₁ (state sig₁) (parlang_mcl_global sig₁) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (parlang_mcl_global sig₂) → vector bool n₂ → Prop)
    (k₁ : mclk sig₁) (k₂ : mclk sig₂)
    (Q : Π n₁:ℕ, parlang.state n₁ (state sig₁) (parlang_mcl_global sig₁) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (state sig₂) (parlang_mcl_global sig₂) → vector bool n₂ → Prop) := 
rel_hoare_state P (mclk_to_kernel k₁) (mclk_to_kernel k₂) Q

inductive mclp (sig : signature)
| intro (f : memory (parlang_mcl_global sig) → ℕ) (k : mclk sig) : mclp

def mclp_to_program {sig : signature} : mclp sig → parlang.program (state sig) (parlang_mcl_global sig)
| (mclp.intro f k) := parlang.program.intro f (mclk_to_kernel k)

end mcl

namespace tactic.interactive

open mcl tactic

-- meta def unfold_to_parlang : tactic unit := do
--     rw ``mclp_to_program
    -- rw mclk_to_kernel,
    -- rw prepend_load_expr,
    -- rw load_global_vars_for_expr,
    -- unfold append,
    -- rw list.append,
    -- rw parlang.list_to_kernel_seq,
    -- repeat {rw list.foldl},

end tactic.interactive

namespace mcl

open mclk

def empty_state {sig : signature} : state sig := λ name idx, default (type_map (type_of (sig name)))

-- we need an assumption on the signature, i.e. tid must be int
def mcl_init {sig : signature} : ℕ → state sig := λ n : ℕ, empty_state.update' (show type_of (sig "tid") = type.int, by sorry) (show (sig "tid").type.dim = ([1] : vector ℕ 1).length, by sorry) n

def mclp_rel {sig₁ sig₂ : signature} (P) (p₁ : mclp sig₁) (p₂ : mclp sig₂) (Q) := rel_hoare_program mcl_init mcl_init P (mclp_to_program p₁) (mclp_to_program p₂) Q

--def eq_assert (sig₁ : signature) : state_assert sig₁ sig₁ := λ n₁ s₁ ac₁ n₂ s₂ ac₂, n₁ = n₂ ∧ s₁ = s₂ ∧ ac₁ = ac₂

-- we have to show some sort of non-interference
example {sig : signature} {n} {k₁} {P Q : state_assert sig sig} (h : sig "i" = { scope := scope.global, type := ⟨_, [0], type.int⟩}) (hpi : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → n₁ = n ∧ n₂ = 1) : 
mclk_rel P k₁ (for "i" h _ 0 (λ s, s.get' h < n) (tlocal_assign "i" (var "i" (by refl) + (const_int 1 h))) k₁) Q := begin
    sorry
end

example {t : type} {n : string} {sig₁ sig₂ : signature} {P Q} {expr} {k₂ : mclk sig₂} (hu : ¬expr_reads n expr)
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