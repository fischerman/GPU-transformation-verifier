
import parlang.defs
open parlang

notation `v[` v:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := v

namespace mcl
variables {n : ℕ}

inductive type
| int
| float
| bool

open type

instance : has_sizeof type :=
⟨λt, match t with
| type.int := 1
| type.float := 1
| type.bool := 2
end⟩

structure array :=
(dim : ℕ)
(type : type)
-- (sizes : vector ℕ dim)

inductive scope
| tlocal
| global

structure variable_def :=
(type : array)
(scope : scope)

@[reducible]
def signature_core := string → variable_def

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

def signature := { sig : signature_core // type_of (sig "tid") = type.int ∧ (sig "tid").type.dim = (v[0] : vector ℕ 1).length}

-- todo: make sig parameter (instead of variable). That way I don't have to mention signature anywhere (see section 6.2)
variables {sig : signature}

@[reducible]
def lean_type_of : variable_def → Type := λ v, type_map (type_of v)
@[reducible]
def signature.type_of (n : string) (sig :signature) := type_of (sig.val n)
@[reducible]
def signature.lean_type_of (n : string) (sig : signature) := lean_type_of (sig.val n)
@[reducible]
def is_tlocal (v : variable_def) := v.scope = scope.tlocal
@[reducible]
def is_global : variable_def → Prop := λ v, v.scope = scope.global

-- @[reducible]
-- def create_signature : list (string × variable_def) → signature
-- | [] n := { scope := scope.tlocal, type := ⟨1, int⟩} -- by default all variables are tlocal int's
-- | ((m, v) :: xs) n := if m = n then v else create_signature xs n

-- if we compare two variable accesses to the same array: when using vectors we only have to reason about equality of elements, otherwise we have to reason about length as well
@[reducible]
def mcl_address (sig : signature) := (Σ n: string, vector ℕ (sig.val n).type.dim)
@[reducible]
def parlang_mcl_global (sig : signature) := (λ i : mcl_address sig, sig.lean_type_of i.1)
@[reducible]
def parlang_mcl_tlocal (sig : signature) := (λ i : mcl_address sig, sig.lean_type_of i.1)
@[reducible]
def parlang_mcl_kernel (sig : signature) := kernel (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)

lemma address_eq {sig : mcl.signature} {a b : mcl.mcl_address sig} (h : a.1 = b.1) (g: a.2 = begin rw h, exact b.2 end) : a = b := sorry

-- expression is an inductive family over types
-- type is called an index
inductive expression (sig : signature) : type → Type
| tlocal_var {t} {dim : ℕ} (n : string) (idx : fin dim → (expression int)) (h₁ : type_of (sig.val n) = t) (h₂ : (sig.val n).type.dim = dim) (h₃ : is_tlocal (sig.val n)) : expression t
| global_var {t} {dim : ℕ} (n : string) (idx : fin dim → (expression int)) (h₁ : type_of (sig.val n) = t) (h₂ : (sig.val n).type.dim = dim) (h₃ : is_global (sig.val n)) : expression t
| add {t} : expression t → expression t → expression t
| literal_int {} {t} (n : ℕ) (h : t = type.int) : expression t
| lt {t} (h : t = type.bool) : expression int → expression int → expression t

open expression

instance (t : type) : has_add (expression sig t) := ⟨expression.add⟩
instance : has_zero (expression sig int) := ⟨expression.literal_int 0 rfl⟩
instance : has_one (expression sig int) := ⟨expression.literal_int 1 rfl⟩
infix < := expression.lt (show type.bool = type.bool, by refl)
notation `v(` n `)`:= expression.tlocal_var n (by refl)
notation `i(` n `)`:= expression.literal_int n (by refl)

def type_map_add : Π{t : type}, type_map t → type_map t → type_map t
| int a b := a + b
| float a b := a + b
| bool a b := a ∧ b

-- we have C on idx
-- use recursor directly
#print expression.rec_on
#print expression.brec_on
#print nat.rec_on
#check ((λ n, nat.rec_on n _ _) : ℕ → ℕ)

-- pattern matching does not work due to problems with the parser
-- implicit argument C of recursor is filled in by the special elaborator "eliminator"
-- arguments sig t and expr must be named, otherwise the eliminator elaborator fails
def expression_size {sig : signature} {t : type} (expr : expression sig t) : ℕ := expression.rec_on expr 
    -- tlocal
    (λ t dim n idx h₁ h₂ h₃ ih, 1 + ((list.range_fin dim).map ih).sum)
    -- global
    (λ t dim n idx h₁ h₂ h₃ ih, 1 + ((list.range_fin dim).map ih).sum)
    -- add
    (λ t a b ih_a ih_b, (1 : ℕ) + (ih_a : ℕ) + (ih_b : ℕ))
    -- literal_int
    (λ t n h, (n : ℕ))
    -- lt
    (λ t h a b ih_a ih_b, ih_a + ih_b + 1)

-- def s₁ : signature
-- | _ := { scope := scope.global, type := ⟨1, type.int⟩ }
-- -- appearently not true
-- def test : (7 : expression s₁ int) = (literal_int 7 (by refl)) := begin
--     sorry, -- not by refl
-- end
-- def idx₁ : fin 1 → expression s₁ int
-- | _ := 7
-- #eval expression_size (tlocal_var "n" idx₁ sorry sorry sorry  : expression s₁ int)
-- #eval expression_size (expression.add (literal_int 123 (by refl)) (literal_int 123 (by refl)) : expression s₁ int)

#print expression_size

@[simp]
lemma abc (t) (expr : expression sig t) : 0 < expression_size expr := sorry

#print psigma.has_well_founded
#print psigma.lex
#print has_well_founded_of_has_sizeof 
#print expression.sizeof

def vector_mpr {α : Type} {dim : ℕ} {sig : signature} {n} (h : (((sig.val n).type).dim) = dim) (v : vector α dim) : vector α (((sig.val n).type).dim) := begin
    rw h,
    exact v,
end

lemma vector_mpr_singleton {α : Type} {a : α} {sig : signature} {n} (h : (((sig.val n).type).dim) = 1) : vector_mpr h v[a] = eq.mpr (by rw h) v[a] := sorry

@[simp]
lemma vector_mpr_rfl {sig : signature} {n} {α : Type} {h : (((sig.val n).type).dim) = (((sig.val n).type).dim)} {v : vector α (((sig.val n).type).dim)} : vector_mpr h v = v := by refl

-- should we make this an inductive predicate
-- it would have implications on parlang
-- might have to change this to rec_on
def eval {sig : signature} (s : memory $ parlang_mcl_tlocal sig) {t : type} (expr : expression sig t) : type_map t := expression.rec_on expr 
    -- tlocal
    (λ t dim n idx h₁ h₂ h₃ ih, by rw ← h₁; exact s.get ⟨n, vector_mpr h₂ $ (vector.range_fin dim).map ih⟩)
    -- global
    -- requires that the global variable has been loaded into tstate under the same name
    (λ t dim n idx h₁ h₂ h₃ ih, by rw ← h₁; exact s.get ⟨n, vector_mpr h₂ $ (vector.range_fin dim).map ih⟩)
    -- add
    (λ t a b ih_a ih_b, type_map_add ih_a ih_b)
    -- literal_int
    (λ t n h, (by rw [h]; exact n))
    -- lt
    (λ t h a b ih_a ih_b, (by rw h; exact (ih_a < ih_b)))

def load_global_vars_for_expr {sig : signature} {t : type} (expr : expression sig t) : list (parlang_mcl_kernel sig) := expression.rec_on expr 
    -- tlocal
    (λ t dim n idx h₁ h₂ h₃ ih, ((list.range_fin dim).map ih).foldl list.append [])
    -- global
    -- requires that the global variable has been loaded into tstate under the same name
    (λ t dim n idx h₁ h₂ h₃ ih, ((list.range_fin dim).map ih).foldl list.append [] ++ [(kernel.load (λ s, ⟨⟨n, vector_mpr h₂ $ ((vector.of_fn idx).map (eval s))⟩, λ v, s.update ⟨n, vector_mpr h₂ $ (vector.of_fn idx).map (eval s)⟩ v⟩) : parlang_mcl_kernel sig)])
    -- add
    (λ t a b ih_a ih_b, ih_a ++ ih_b)
    -- literal_int
    (λ t n h, [])
    -- lt
    (λ t h a b ih_a ih_b, ih_a ++ ih_b)

def prepend_load_expr {sig : signature} {t : type} (expr : expression sig t) (k : parlang_mcl_kernel sig) :=
(load_global_vars_for_expr expr).foldr kernel.seq k
--list_to_kernel_seq (load_global_vars_for_expr expr ++ [k])

def append_load_expr  {sig : signature} {t : type} (expr : expression sig t) (k : parlang_mcl_kernel sig) :=
(load_global_vars_for_expr expr).foldl kernel.seq k
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

def expr_reads (n : string) {t : type} (expr : expression sig t) : _root_.bool := expression.rec_on expr
    -- tlocal
    (λ t dim m idx h₁ h₂ h₃ ih, (m = n) || ((list.range_fin dim).map ih).any id)
    -- global
    (λ t dim m idx h₁ h₂ h₃ ih, (m = n) || ((list.range_fin dim).map ih).any id)
    -- add
    (λ t a b ih_a ih_b, ih_a || ih_b)
    -- literal_int
    (λ t n h, ff)
    -- lt
    (λ t h a b ih_a ih_b, ih_a || ih_b)

lemma eval_update_ignore {sig : signature} {t t₂ : type} {n} {idx₂ : vector ℕ ((sig.val n).type).dim} {v} {expr : expression sig t} {s : memory $ parlang_mcl_tlocal sig} (h : expr_reads n expr = ff) : 
eval (s.update ⟨n, idx₂⟩ v) expr = eval s expr := begin
    admit
end

-- can we make use of functor abstraction
lemma eval_update_ignore' {sig : signature} {t t₂ : type} {dim n} {idx₂ : vector ℕ ((sig.val n).type).dim} {v} {idx : vector (expression sig t) dim} {s : memory $ parlang_mcl_tlocal sig} (h : (idx.to_list.all $ bnot ∘ expr_reads n) = tt) : 
vector.map (eval (s.update ⟨n, idx₂⟩ v)) idx = vector.map (eval s) idx := begin
    admit
end

-- TODO variable assign constructors should include global and local proof
-- expression sig (type_of (sig n)) is not definitionally equal if sig is not computable
inductive mclk (sig : signature)
| tlocal_assign {t : type} {dim : ℕ} (n : string) (idx : vector (expression sig int) dim) (h₁ : type_of (sig.val n) = t) (h₂ : (sig.val n).type.dim = idx.length) : (expression sig t) → mclk
| global_assign {t : type} {dim : ℕ} (n) (idx : vector (expression sig int) dim) (h₁ : type_of (sig.val n) = t) (h₂ : (sig.val n).type.dim = idx.length) : (expression sig t) → mclk
| seq : mclk → mclk → mclk
| for (n : string) (h : sig.type_of n = int) (h₂ : (sig.val n).type.dim = 1) :
  expression sig int → expression sig bool → mclk → mclk → mclk
| skip {} : mclk

infixr ` ;; `:90 := mclk.seq

open mclk

def mclk_reads (n : string) : mclk sig → _root_.bool
| (tlocal_assign _ idx _ _ expr) := expr_reads n expr || (idx.to_list.any (λ e, expr_reads n e))
| (global_assign _ idx _ _ expr) := expr_reads n expr || (idx.to_list.any (λ e, expr_reads n e))
| (seq k₁ k₂) := mclk_reads k₁ || mclk_reads k₂
| (for _ _ _ init c inc body) := expr_reads n init || expr_reads n c || mclk_reads inc || mclk_reads body
| (skip) := false

--lemma mclk_expr_reads (k) : mclk_reads n k → ∃ expr, (expr_reads n expr ∧ subexpr expr k)

def mclk_to_kernel {sig : signature} : mclk sig → parlang_mcl_kernel sig
| (seq k₁ k₂) := kernel.seq (mclk_to_kernel k₁) (mclk_to_kernel k₂)
| (skip) := kernel.compute id
| (tlocal_assign n idx h₁ h₂ expr) := prepend_load_expr expr (kernel.compute (λ s, s.update ⟨n, vector_mpr h₂ $  idx.map (eval s)⟩ (begin unfold parlang_mcl_tlocal signature.lean_type_of lean_type_of, rw h₁, exact (eval s expr) end)))
| (global_assign n idx h₁ h₂ expr) := prepend_load_expr expr (kernel.compute (λ s, s.update ⟨n, vector_mpr h₂ $  idx.map (eval s)⟩ (begin unfold parlang_mcl_tlocal signature.lean_type_of lean_type_of, rw h₁, exact (eval s expr) end))) ;; kernel.store (λ s, ⟨⟨n, vector_mpr h₂ $ idx.map (eval s)⟩, s.get ⟨n, vector_mpr h₂ $ idx.map (eval s)⟩⟩)
| (for n h h₂ expr c k_inc k_body) := prepend_load_expr expr (kernel.compute (λ s, s.update ⟨n, vector_mpr h₂ $  v[eval s expr]⟩ (begin unfold parlang_mcl_tlocal signature.lean_type_of lean_type_of, unfold signature.type_of at h, rw h, exact eval s expr end))) ;; 
    prepend_load_expr c (
        kernel.loop (λ s, eval s c) (mclk_to_kernel k_body ;; append_load_expr c (mclk_to_kernel k_inc))
    )

-- if a kernel does not contain a global referencce it must not contain any loads
example (k : mclk sig) (h : ∀ n, is_global (sig.val n) → ¬mclk_reads n k) : ∀ sk, subkernel sk (mclk_to_kernel k) → ¬∃ f, sk = (kernel.load f) := begin
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
                        unfold mclk_reads,
                        sorry,
                    }, {
                        assumption,
                    }
                }, {
                    apply k_ih_a_1,
                    {
                        intros n hg hr,
                        apply h n hg,
                        sorry,
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

inductive mclp (sig : signature)
| intro (f : memory (parlang_mcl_global sig) → ℕ) (k : mclk sig) : mclp

def mclp_to_program {sig : signature} : mclp sig → parlang.program (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)
| (mclp.intro f k) := parlang.program.intro f (mclk_to_kernel k)

def empty_state {sig : signature} : (memory $ parlang_mcl_tlocal sig) := λ var, default (type_map (type_of (sig.val var.1)))

-- we need an assumption on the signature, i.e. tid must be int
def mcl_init {sig : signature} : ℕ → (memory $ parlang_mcl_tlocal sig) := λ n : ℕ, empty_state.update ⟨"tid", begin rw sig.property.right, exact v[0] end⟩ (begin unfold parlang_mcl_tlocal signature.lean_type_of lean_type_of, rw sig.property.left, exact n end)

end mcl