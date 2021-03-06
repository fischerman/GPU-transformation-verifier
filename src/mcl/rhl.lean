import mcl.defs
import parlang.rhl

namespace mcl
namespace rhl

open parlang
open mclk

@[reducible]
def state_assert (sig₁ sig₂ : signature) := Π n₁:ℕ, parlang.state n₁ (memory (parlang_mcl_tlocal sig₁)) (parlang_mcl_shared sig₁) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (memory (parlang_mcl_tlocal sig₂)) (parlang_mcl_shared sig₂) → vector bool n₂ → Prop

def mclk_rel {sig₁ sig₂ : signature} 
    (P : state_assert sig₁ sig₂)
    (k₁ : mclk sig₁) (k₂ : mclk sig₂)
    (Q : state_assert sig₁ sig₂) := 
rel_hoare_state P (mclk_to_kernel k₁) (mclk_to_kernel k₂) Q

notation `{* ` P : 1 ` *} ` k₁ : 1 ` ~> ` k₂ : 1 ` {* ` Q : 1 ` *}` := mclk_rel P k₁ k₂ Q

def mclp_rel {sig₁ sig₂ : signature} (P) (p₁ : mclp sig₁) (p₂ : mclp sig₂) (Q) := rel_hoare_program mcl_init mcl_init P (mclp_to_program p₁) (mclp_to_program p₂) Q

--def eq_assert (sig₁ : signature) : state_assert sig₁ sig₁ := λ n₁ s₁ ac₁ n₂ s₂ ac₂, n₁ = n₂ ∧ s₁ = s₂ ∧ ac₁ = ac₂

-- we have to show some sort of non-interference
-- example {sig : signature} {n} {k₁} {P Q : state_assert sig sig} (h : sig "i" = { scope := scope.shared, type := ⟨_, [0], type.int⟩}) (hpi : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → n₁ = n ∧ n₂ = 1) : 
-- mclk_rel P k₁ (for "i" h _ 0 (λ s, s.get' h < n) (tlocal_assign "i" (var "i" (by refl) + (literal_int 1 h))) k₁) Q := begin
--     sorry
-- end

-- example {t : type} {n : string} {sig₁ sig₂ : signature} {P Q} {expr} {k₂ : mclk sig₂} (hu : ¬expr_reads n expr)
-- (hr : @mclk_rel sig₁ sig₂ P (tlocal_assign n idx _ _ expr ;; tlocal_assign n idx _ _ expr) k₂ Q) : 
-- @mclk_rel sig₁ sig₂ P (tlocal_assign n expr) k₂ Q := begin
--     unfold mclk_rel,
--     rw mclk_to_kernel,
--     intros _ _ _ _ _ _ _ hp hek₁,
--     specialize hr n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ hp,
--     apply hr,
--     unfold mclk_to_kernel,
--     apply exec_state.seq,
--     {
--         apply exec_state.compute,
--     }, {
--         suffices : s₁' = state.map_active_threads ac₁ (thread_state.map (λ (s : state sig₁), state.update' _ (eval expr s) s)) (state.map_active_threads ac₁ (thread_state.map (λ (s : state sig₁), state.update' _ (eval expr s) s)) s₁),
--         {
--             subst this,
--             apply exec_state.compute,
--         }, {
--             sorry,
--         }
--     }
-- end

variables {sig sig₁ sig₂ : signature} {k₁ k₁' : mclk sig₁} {k₂ k₂' : mclk sig₂} {P P' Q Q' R : Π n₁:ℕ, parlang.state n₁ (memory $ parlang_mcl_tlocal sig₁) (parlang_mcl_shared sig₁) → vector bool n₁ → Π n₂:ℕ, parlang.state n₂ (memory $ parlang_mcl_tlocal sig₂) (parlang_mcl_shared sig₂) → vector bool n₂ → Prop}

lemma rel_mclk_to_mclp {sig₁ sig₂ : signature} (f₁ : memory (parlang_mcl_shared sig₁) → ℕ) (f₂ : memory (parlang_mcl_shared sig₂) → ℕ)
(P Q : memory (parlang_mcl_shared sig₁) → memory (parlang_mcl_shared sig₂) → Prop)
(k₁ : mclk sig₁) (k₂ : mclk sig₂) (h : mclk_rel 
(λ n₁ s₁ ac₁ n₂ s₂ ac₂, ∃ m₁ m₂, initial_kernel_assertion mcl_init mcl_init P f₁ f₂ m₁ m₂ n₁ s₁ ac₁ n₂ s₂ ac₂)
    k₁ k₂ 
(λ n₁ s₁ ac₁ n₂ s₂ ac₂, (∃ m₁, s₁.syncable m₁) → ∃ m₁ m₂, s₁.syncable m₁ ∧ s₂.syncable m₂ ∧ Q m₁ m₂))
(hg : ∀ {m₁ m₂}, P m₁ m₂ → 0 < f₁ m₁) : 
mclp_rel P (mclp.intro f₁ k₁) (mclp.intro f₂ k₂) Q := rel_kernel_to_program h @hg

-- lemma assign_swap {sig : signature} {t : type} (n₁ n₂) (dim₁ dim₂) (idx₁ : vector (expression sig type.int) dim₁) (idx₂ : vector (expression sig type.int) dim₂) (h₁ h₂) (expr₁ : expression sig (type_of (sig n₁))) (expr₂ : expression sig (type_of (sig n₂))) (q) (ac : vector _ q) (s u) : 
-- exec_state (mclk_to_kernel ((tlocal_assign n₁ idx₁ h₁ expr₁) ;; tlocal_assign n₂ idx₂ h₂ expr₂)) ac s u →
-- exec_state (mclk_to_kernel ((tlocal_assign n₂ idx₂ h₂ expr₂) ;; (tlocal_assign n₁ idx₁ h₁ expr₁))) ac s u := begin
--     intro h,
--     cases h,
--     rename h_t t,
--     rename h_a hl,
--     rename h_a_1 hr,
--     -- break out the compute and replace it with skip
--     apply exec_state.seq,
--     {

--     }
-- end

--todo define interference (maybe choose another name) and define swap on non-interference
--lemma rel_assign_swap {sig₁ sig₂ : signature} 

/-- Prepend skip to the left program -/
lemma add_skip_left : {* P *} k₁ ~> k₂ {* Q *} ↔ 
{* P *} skip ;; k₁ ~> k₂ {* Q *} := begin
    -- this only solves ltr
    unfold mclk_rel,
    apply iff.intro,
    {
        intro h,
        intros n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ hp he₁,
        apply h,
        exact hp,
        cases he₁,
        cases he₁_a,
        sorry --trivial from he₁_a_1
    }, {
        intro h,
        intros n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ hp he₁,
        apply h,
        exact hp,
        apply exec_state.seq _ _ _ _ _ _ _ he₁,
        sorry,
    }
end

lemma skip_left_after : {* P *} k₁ ~> k₂ {* Q *} ↔ 
{* P *} k₁ ;; skip ~> k₂ {* Q *} := sorry
lemma skip_right : {* P *} k₁ ~> k₂ {* Q *} ↔ 
{* P *}  k₁ ~> skip ;; k₂ {* Q *} := sorry
lemma skip_right_after : {* P *} k₁ ~> k₂ {* Q *} ↔ 
{* P *} k₁ ~> k₂ ;; skip {* Q *} := sorry

lemma single_step_left :
{* P *} k₁ ~> skip {* Q *} →
{* Q *} k₁' ~> k₂ {* R *} →
{* P *} (k₁ ;; k₁') ~> k₂ {* R *} := parlang.single_step_left Q

@[irreducible]
def exprs_to_indices {n dim} {idx : vector (expression sig type.int) dim} (h : ((sig.val n).type).dim = vector.length idx) (s : (memory $ parlang_mcl_tlocal sig)) : 
(sig.val n).type.dim = (idx.map (eval s)).length := h

open expression

lemma seq (Q) (h₁ : {* P *} k₁ ~> k₂ {* Q *}) (h₂ : {* Q *} k₁' ~> k₂' {* R *}) :
{* P *} k₁ ;; k₁' ~> k₂ ;; k₂' {* R *} := parlang.seq Q h₁ h₂

lemma seq_left {P R} (Q) (h₁ : {* P *} k₁ ~> skip {* Q *}) (h₂ : {* Q *} k₁' ~> k₂' {* R *}) :
mclk_rel P (k₁ ;; k₁') k₂' R := skip_right.mpr (seq Q h₁ h₂)

lemma consequence (h : {* P *} k₁ ~> k₂ {* Q *})
(hp : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P' n₁ s₁ ac₁ n₂ s₂ ac₂ → P n₁ s₁ ac₁ n₂ s₂ ac₂)
(hq : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, Q n₁ s₁ ac₁ n₂ s₂ ac₂ → Q' n₁ s₁ ac₁ n₂ s₂ ac₂) : 
{* P' *} k₁ ~> k₂ {* Q' *} := consequence h hp hq

lemma swap_skip (h : {* parlang.assertion_swap_side P *} skip ~> k₁ {* parlang.assertion_swap_side Q *}) : 
{* P *} k₁ ~> skip {* Q *} := begin
    apply parlang.swap h,
    intros,
    use s₁,
    apply exec_skip,
end

-- todo relate to load_shared_vars_for_expr
/-- Copy values from shared to tlocal memory for all occurences of shared variables in *expr*. If there are no references, this definition is equal to *id*. This definition is the equivalent of load_shared_vars_for_expr for *thread_state*. -/
def thread_state.update_shared_vars_for_expr {t : type} (expr : expression sig t) : 
thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig) :=
expression.rec_on expr 
    -- tlocal
    (λ t dim n idx h₁ h₂ h₃ ih, id)
    -- shared
    (λ t dim n idx h₁ h₂ h₃ ih, λ ts,
    ((list.range_fin dim).foldl (λ ts e, ih e ts) ts
    ).load (λ m, ⟨mcl_addr_from_var h₂ (vector.of_fn idx) m, λ v, m.update (mcl_addr_from_var h₂ (vector.of_fn idx) m) v⟩))
    -- add
    (λ t a b ih_a ih_b, ih_b ∘ ih_a)
    -- mult
    (λ t a b ih_a ih_b, ih_b ∘ ih_a)
    -- literal_int
    (λ t n h, id)
    -- lt
    (λ t h a b ih_a ih_b, ih_b ∘ ih_a)

/-- Lifts *thread_state.update_shared_vars_for_expr* to a vector -/
def thread_state.update_shared_vars_for_exprs {n} {t : type} (exprs : vector (expression sig t) n) : 
thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig) :=
λts, exprs.to_list.foldr (λexpr ts, thread_state.update_shared_vars_for_expr expr ts) ts

-- TODO: change to double implication
/-- Resolve semantics of loading_shared_vars_for_expr to the relation on state -/
lemma update_load_shared_vars_for_expr {sig t} {expr : expression sig t} {n} {ac : vector bool n} {s u} : 
exec_state (list.foldr kernel.seq (kernel.compute id) (load_shared_vars_for_expr expr)) ac s u ↔ 
u = s.map_active_threads ac (thread_state.update_shared_vars_for_expr expr) := begin
    sorry,
    -- apply iff.intro,
    -- {
    --     induction expr generalizing s u,
    --     case mcl.expression.tlocal_var {
    --         intro h,
    --         delta thread_state.update_shared_vars_for_expr,
    --         unfold load_shared_vars_for_expr at h,
    --         cases h,
    --         have : (λ (a : state sig), a) = id := by refl,
    --         rw this,
    --         rw ← parlang.state.map_active_threads_id s ac,
    --         simp [state.map_active_threads],
    --         sorry,
    --     },
    --     case mcl.expression.shared_var {
    --         cases h,
    --         cases h_a_1,
    --         cases h_a,
    --         have : (λ (a : state sig), a) = id := by refl,
    --         rw this,
    --         sorry,
    --     },
    --     case mcl.expression.add {
    --         rw load_shared_vars_for_expr at h,
    --         simp at h,
    --         rw kernel_foldr_skip at h,
    --         cases h,
    --         specialize expr_ih_a h_a,
    --         specialize expr_ih_a_1 h_a_1,
    --         subst expr_ih_a_1,
    --         subst expr_ih_a,
    --         rw parlang.state.map_map_active_threads',
    --         refl,
    --     },
    --     case mcl.expression.literal_int {
    --         cases h,
    --         sorry,
    --     },
    --     case mcl.expression.lt {
    --         rw load_shared_vars_for_expr at h,
    --         simp at h,
    --         rw kernel_foldr_skip at h,
    --         cases h,
    --         specialize expr_ih_a h_a,
    --         specialize expr_ih_a_1 h_a_1,
    --         subst expr_ih_a_1,
    --         subst expr_ih_a,
    --         rw parlang.state.map_map_active_threads',
    --         refl,
    --     }
    -- }
end

lemma update_load_shared_vars_for_exprs {sig t m} {exprs : vector (expression sig t) m} {n} {ac : vector bool n} {s u} : 
exec_state (exprs.to_list.foldr (λexpr' k, prepend_load_expr expr' k) (kernel.compute id)) ac s u ↔ 
u = s.map_active_threads ac (thread_state.update_shared_vars_for_exprs exprs) := begin
    unfold thread_state.update_shared_vars_for_exprs,
    cases exprs,
    simp,
    sorry, -- induction exprs_val and update_load_shared_vars_for_expr
end

lemma foldr_prepend_load_expr_skip {sig t} {k : kernel (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)} {n} {s u} {ac : vector bool n} {v : list $ expression sig t} : exec_state
    (list.foldr (λ expr' k, prepend_load_expr expr' k) k v)
    ac s u ↔
    exec_state 
    ((list.foldr (λ expr' k, prepend_load_expr expr' k) (kernel.compute id) v) ;; k)
    ac s u := sorry

/-- Single-sided inference rule -/
lemma update_load_shared_vars_for_expr_right {t} {expr : expression sig₂ t} : 
{* λn₁ s₁ ac₁ n₂ (s₂ : state n₂ (memory (parlang_mcl_tlocal sig₂)) (parlang_mcl_shared sig₂)) ac₂, P n₁ s₁ ac₁ n₂ (s₂.map_active_threads ac₂ (thread_state.update_shared_vars_for_expr expr)) ac₂ *} 
kernel.compute id ~> list.foldr kernel.seq (kernel.compute id) (load_shared_vars_for_expr expr) 
{* P *} := begin
    intros _ _ _ _ _ _ _ hp he,
    use (s₂.map_active_threads ac₂ (thread_state.update_shared_vars_for_expr expr)),
    split, {
        rw update_load_shared_vars_for_expr,
    }, {
        cases he,
        sorry, -- trivial
    }
end

def f := λ n, n * 2
def g := λ(n : nat), n + 1
#check g
#eval (f ∘ g) 4

-- TODO should this moved to defs?
/-- Stores the locally computed value in the shadow memory. This is an abstraction over *thread_state.store*, which hides the lambda-term. This makes it easier to rewrite. -/
@[irreducible]
def thread_state.tlocal_to_shared {sig : signature} {t} {dim} (var : string) (idx : vector (expression sig type.int) dim) (h₁ : type_of (sig.val var) = t) (h₂ : ((sig.val var).type).dim = dim) := 
@thread_state.store _ _ (parlang_mcl_shared sig) _ (λ (m : memory $ parlang_mcl_tlocal sig), ⟨mcl_addr_from_var h₂ idx m, m.get $ mcl_addr_from_var h₂ idx m⟩)

/-- Evaluates an expressions and assigns the value -/
def thread_state.assign_expr {sig : signature} (var) (expr : expression sig $ sig.type_of var)
(idx : vector (expression sig type.int) (sig.val var).type.dim) :=
@thread_state.compute (memory $ parlang_mcl_tlocal sig) _ (parlang_mcl_shared sig) _
    $ λs, s.update ⟨var, idx.map (eval s)⟩ $ eval s expr


/-- Processes a single tlocal assign on the right side. Proven by operational semantics -/
lemma tlocal_assign_right {var} 
{expr : expression sig₂ $ sig₂.type_of var}
{idx : vector (expression sig₂ type.int) (sig₂.val var).type.dim} :
{* (λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ 
    ((s₂ : parlang.state n₂ (memory $ parlang_mcl_tlocal sig₂) (parlang_mcl_shared sig₂)).map_active_threads ac₂ (
        thread_state.assign_expr var expr idx ∘ 
        thread_state.update_shared_vars_for_expr expr
    )) ac₂) *}
(skip : mclk sig₁) ~> tlocal_assign var idx rfl rfl expr {* P *} := begin
    unfold mclk_rel,
    unfold mclk_to_kernel,
    unfold prepend_load_expr,
    sorry,
end

-- lemma tlocal_assign_right {t dim n expr} {idx : vector (expression sig₂ type.int) dim} {h₁ : type_of (sig₂ n) = t} {h₂ : ((sig₂ n).type).dim = vector.length idx} : 
-- mclk_rel (λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ (s₂.map_active_threads ac₂ (λ ts, (thread_state.update_shared_vars_for_expr expr ts).map (λ s, s.update' h₁ (exprs_to_indices h₂ s) (eval s expr)))) ac₂) (skip : mclk sig₁) (tlocal_assign n idx h₁ h₂ expr) P := begin
--     intros n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ hp he₁,
--     use (s₂.map_active_threads ac₂ (λ ts, (thread_state.update_shared_vars_for_expr expr ts).map (λ s, s.update' h₁ (exprs_to_indices h₂ s) (eval s expr)))),
--     split, {
--         unfold mclk_to_kernel,
--         unfold prepend_load_expr,
--         rw kernel_foldr_skip,
--         apply exec_state.seq,
--         {
--             rw update_load_shared_vars_for_expr,
--         }, {
--             rw [← parlang.state.map_map_active_threads'],
--             apply exec_state.compute,
--         }
--     }, {
--         have : s₁ = s₁' := sorry, -- trivial skip
--         subst this,
--         exact hp,
--     }
-- end

-- lemma tlocal_assign_right' {t dim n expr} {idx : vector (expression sig₂ type.int) dim} {h₁ : type_of (sig₂ n) = t} {h₂ : ((sig₂ n).type).dim = vector.length idx} 
-- (hi : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → Q n₁ s₁ ac₁ n₂ (s₂.map_active_threads ac₂ (λ ts, (thread_state.update_shared_vars_for_expr ts expr).map (λ s, s.update' h₁ (exprs_to_indices h₂ s) (eval s expr)))) ac₂) : 
-- mclk_rel P (skip : mclk sig₁) (tlocal_assign n idx h₁ h₂ expr) Q := begin
--     apply consequence tlocal_assign_right hi,
--     intros _ _ _ _ _ _ _,
--     assumption,
-- end

-- lemma tlocal_assign_left {t dim n expr} {idx : vector (expression sig₁ type.int) dim} {h₁ : type_of (sig₁ n) = t} {h₂ : ((sig₁ n).type).dim = vector.length idx} : 
-- mclk_rel (λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ (s₁.map_active_threads ac₁ (λ ts, (thread_state.update_shared_vars_for_expr ts expr).map (λ s, s.update' h₁ (exprs_to_indices h₂ s) (eval s expr)))) ac₁ n₂ s₂ ac₂) 
-- (tlocal_assign n idx h₁ h₂ expr) (skip : mclk sig₂) P := begin
--     apply swap_skip tlocal_assign_right,
-- end

-- lemma tlocal_assign_left' {t dim n expr} {idx : vector (expression sig₁ type.int) dim} {h₁ : type_of (sig₁ n) = t} {h₂ : ((sig₁ n).type).dim = vector.length idx} 
-- (hi : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → Q n₁ (s₁.map_active_threads ac₁ (λ ts, (thread_state.update_shared_vars_for_expr ts expr).map (λ s, s.update' h₁ (exprs_to_indices h₂ s) (eval s expr)))) ac₁ n₂ s₂ ac₂) : 
-- mclk_rel P (tlocal_assign n idx h₁ h₂ expr) (skip : mclk sig₂) Q := begin
--     apply consequence tlocal_assign_left hi,
--     intros _ _ _ _ _ _ _,
--     assumption,
-- end

-- todo define in terms of 
/-- Processes a single shared assign on the right side. Proven by operational semantics -/
lemma shared_assign_right'' {var} 
{expr : expression sig₂ $ sig₂.type_of var}
{idx : vector (expression sig₂ type.int) (sig₂.val var).type.dim} :
{* (λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ 
    ((s₂ : parlang.state n₂ (memory $ parlang_mcl_tlocal sig₂) (parlang_mcl_shared sig₂)).map_active_threads ac₂ (
        thread_state.tlocal_to_shared var idx rfl rfl ∘
        thread_state.assign_expr var expr idx ∘ 
        thread_state.update_shared_vars_for_expr expr ∘
        thread_state.update_shared_vars_for_exprs idx
    )) ac₂) *}
(skip : mclk sig₁) ~> shared_assign var idx rfl rfl expr {* P *} := begin
    unfold mclk_rel,
    unfold mclk_to_kernel,
    unfold prepend_load_expr,
    sorry,
end

/-- Processes a single shared assign on the right side. Proven by operational semantics -/
lemma shared_assign_right {t dim n} {idx : vector (expression sig₂ type.int) dim} {h₁ : type_of (sig₂.val n) = t} {h₂ : ((sig₂.val n).type).dim = dim} {expr : expression sig₂ t} : 
{* (λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ 
    ((s₂ : parlang.state n₂ (memory $ parlang_mcl_tlocal sig₂) (parlang_mcl_shared sig₂)).map_active_threads ac₂ (
        thread_state.tlocal_to_shared n idx h₁ h₂ ∘
        thread_state.compute (memory.update_assign n idx h₁ h₂ expr) ∘ 
        thread_state.update_shared_vars_for_expr expr ∘
        thread_state.update_shared_vars_for_exprs idx
    )) ac₂) *}
(skip : mclk sig₁) ~> shared_assign n idx h₁ h₂ expr {* P *} := begin
    intros n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ hp he₁,
    use ((s₂ : parlang.state n₂ (memory $ parlang_mcl_tlocal sig₂) (parlang_mcl_shared sig₂)).map_active_threads ac₂ (
        thread_state.tlocal_to_shared n idx h₁ h₂ ∘
        thread_state.compute (memory.update_assign n idx h₁ h₂ expr) ∘ 
        thread_state.update_shared_vars_for_expr expr ∘
        thread_state.update_shared_vars_for_exprs idx
    )),
    split, {
        unfold mclk_to_kernel,
        rw foldr_prepend_load_expr_skip,
        apply exec_state.seq,
        {
            rw update_load_shared_vars_for_exprs,
        },
        apply exec_state.seq,
        {
            unfold prepend_load_expr,
            rw kernel_foldr_skip,
            apply exec_state.seq,
            {
                rw update_load_shared_vars_for_expr,
            }, {
                apply exec_state.compute,
            }
        }, {
            rw parlang.state.map_map_active_threads',
            rw parlang.state.map_map_active_threads',
            unfold thread_state.tlocal_to_shared,
            rw [← parlang.state.map_map_active_threads' _ (thread_state.store _)],
            apply exec_state.store,
        }
    }, {
        have : s₁ = s₁' := sorry, -- trivial skip
        subst this,
        exact hp,
    },
end

/-- Proven by Parlang inference rules -/
lemma shared_assign_right' {t dim n} {idx : vector (expression sig₂ type.int) dim} {h₁ : type_of (sig₂.val n) = t} {h₂ : ((sig₂.val n).type).dim = dim} {expr : expression sig₂ t} : 
{* (λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ 
    ((s₂ : parlang.state n₂ (memory $ parlang_mcl_tlocal sig₂) (parlang_mcl_shared sig₂)).map_active_threads ac₂ (
        thread_state.tlocal_to_shared n idx h₁ h₂ ∘
        thread_state.compute (λ s : memory $ parlang_mcl_tlocal sig₂, s.update ⟨n, by rw h₂; exact idx.map (eval s)⟩ (begin unfold parlang_mcl_tlocal signature.lean_type_of lean_type_of, rw h₁, exact (eval s expr) end)) ∘ 
        thread_state.update_shared_vars_for_expr expr ∘
        thread_state.update_shared_vars_for_exprs idx
    )) ac₂) *}
(skip : mclk sig₁) ~> shared_assign n idx h₁ h₂ expr {* P *} := begin
    rw skip_left_after,
    rw skip_left_after,
    unfold mclk_rel mclk_to_kernel,
    sorry,
    /- apply parlang.seq,
    swap, {
        apply parlang.store_right,
    }, {
        unfold prepend_load_expr,
        rw kernel_foldr_skip_right,
        apply parlang.seq,
        swap,
        apply parlang.compute_right,
        apply parlang.consequence_pre,
        exact update_load_shared_vars_for_expr_right,
        {
            intros,
            repeat { rw parlang.state.map_map_active_threads },
            sorry,
        }
    } -/
end

lemma shared_assign_left {t dim n expr} {idx : vector (expression sig₁ type.int) dim} {h₁ : type_of (sig₁.val n) = t} {h₂ : ((sig₁.val n).type).dim = vector.length idx} : 
mclk_rel (λ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ 
    ((s₁ : parlang.state n₁ (memory $ parlang_mcl_tlocal sig₁) (parlang_mcl_shared sig₁)).map_active_threads ac₁ (
        thread_state.tlocal_to_shared n idx h₁ h₂ ∘
        thread_state.compute (memory.update_assign n idx h₁ h₂ expr) ∘ 
        thread_state.update_shared_vars_for_expr expr ∘
        thread_state.update_shared_vars_for_exprs idx
    )) ac₁ n₂ s₂ ac₂) 
(shared_assign n idx h₁ h₂ expr) (skip : mclk sig₂) P := begin
    apply swap_skip shared_assign_right,
end

lemma shared_assign_left' {t dim n expr} {idx : vector (expression sig₁ type.int) dim} {h₁ : type_of (sig₁.val n) = t} {h₂ : ((sig₁.val n).type).dim = vector.length idx} 
(hi : ∀ n₁ s₁ ac₁ n₂ s₂ ac₂, P n₁ s₁ ac₁ n₂ s₂ ac₂ → Q n₁ 
    (s₁.map_active_threads ac₁ (
        thread_state.tlocal_to_shared n idx h₁ h₂ ∘
        thread_state.compute (memory.update_assign n idx h₁ h₂ expr) ∘ 
        thread_state.update_shared_vars_for_expr expr ∘
        thread_state.update_shared_vars_for_exprs idx
    )) ac₁ n₂ s₂ ac₂) : 
mclk_rel P (shared_assign n idx h₁ h₂ expr) (skip : mclk sig₂) Q := begin
    apply consequence shared_assign_left hi,
    intros _ _ _ _ _ _ _,
    assumption,
end

end rhl
end mcl