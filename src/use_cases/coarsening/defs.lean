import mcl
import parlang.lemmas_memory

open mcl

namespace coarsening

def sigc : signature_core
| "tid" := { scope := scope.tlocal, type := ⟨1, type.int⟩ }
| "i" := { scope := scope.tlocal, type := ⟨1, type.int⟩ }
| "j" := { scope := scope.tlocal, type := ⟨1, type.int⟩ }
| _ := { scope := scope.shared, type := ⟨1, type.float⟩ }

def sig : signature := ⟨sigc, ⟨rfl, rfl, rfl⟩⟩

open mcl.expression
open parlang

/-- Copies the *j*-th element from a to b -/
def copy : mclk sig := mclk.shared_assign "b" v[@tlocal_var sig _ _ "j" (λ_, 0) rfl rfl rfl] rfl rfl (@shared_var sig _ _ "a" (v[@tlocal_var sig _ _ "j" (λ_, 0) rfl rfl rfl]).nth rfl rfl rfl)

def e₁ := 10
def f₁ := 10
def p₁ : mclp sig := mclp.intro (λ m, e₁) (
    mclk.for "i" rfl rfl (literal_int 0 rfl) (@tlocal_var sig _ _ "i" (λ_, 0) rfl rfl rfl < literal_int f₁ rfl) (mclk.tlocal_assign "i" v[0] rfl rfl $ tlocal_var "i" (λ_, 0) rfl rfl rfl + literal_int 1 rfl) (
        mclk.tlocal_assign "j" v[literal_int 0 rfl] rfl rfl (@tlocal_var sig _ _ "tid" (λ_, 0) rfl rfl rfl * literal_int e₁ rfl + @tlocal_var sig _ _ "i" (λ_, 0) rfl rfl rfl) ;;
        copy
    )
)

def e₂ := 5
def f₂ := 20
def p₂ : mclp sig := mclp.intro (λ m, e₂) (
    mclk.for "i" rfl rfl (literal_int 0 rfl) (@tlocal_var sig _ _ "i" (λ_, 0) rfl rfl rfl < literal_int f₂ rfl) (mclk.tlocal_assign "i" v[0] rfl rfl $ @tlocal_var sig _ _ "i" (λ_, 0) rfl rfl rfl + literal_int 1 rfl) (
        mclk.tlocal_assign "j" v[literal_int 0 rfl] rfl rfl (@tlocal_var sig _ _ "tid" (λ_, 0) rfl rfl rfl * literal_int e₂ rfl + @tlocal_var sig _ _ "i" (λ_, 0) rfl rfl rfl) ;;
        copy
    )
)

def read_tid {sig : signature} := @tlocal_var sig _ _ "tid" (λ_, 0) sig.property.left sig.property.right.left sig.property.right.right

def coarsen_kernel_assertion {sig : signature}
(P : memory (parlang_mcl_shared sig) → memory (parlang_mcl_shared sig) → Prop)
(f₁ : memory (parlang_mcl_shared sig) → ℕ) (f₂ : memory (parlang_mcl_shared sig) → ℕ) 
(m₁ : memory (parlang_mcl_shared sig)) (m₂ : memory (parlang_mcl_shared sig)) 
(n₁) (s₁ : state n₁ (memory $ parlang_mcl_tlocal sig) $ parlang_mcl_shared sig) 
(ac₁ : vector bool n₁) (n₂) (s₂ : state n₂ (memory $ parlang_mcl_tlocal sig) $ parlang_mcl_shared sig) 
(ac₂ : vector bool n₂) := 
s₁.syncable m₁ ∧ s₂.syncable m₂ ∧ n₁ = f₁ m₁ ∧ n₂ = f₂ m₂ ∧
(∀ i : fin n₁, s₁.threads.nth i = { tlocal := mcl_init i, shared := m₁, stores := ∅, loads := ∅ }) ∧ 
(∀ i : fin n₂, s₂.threads.nth i = { tlocal := mcl_init i, shared := m₂, stores := ∅, loads := ∅ }) ∧
P m₁ m₂ ∧ all_threads_active ac₁ ∧ all_threads_active ac₂

/-- only works with constant number of threads -/
theorem coarsen (e₁ e₂) 
(sig) (k₁ : mclk sig) (k₂ : mclk sig) (h₁ : type_of (sig.val "k") = type.int) (h₂ : ((sig.val "k").type).dim = 1) (h₃) (Q : parlang.memory (parlang_mcl_shared sig) → parlang.memory (parlang_mcl_shared sig) → Prop)
(h : rhl.mclk_rel (λn₁ (s₁ : state n₁ (memory (parlang_mcl_tlocal sig)) (parlang_mcl_shared sig)) ac₁ n₂ s₂ ac₂, ∃ m₁ m₂, 
parlang.initial_kernel_assertion mcl_init mcl_init eq (λm, e₁) (λm, e₂) m₁ m₂ n₁ 
(s₁.map_active_threads ac₁ $ λts, ts.compute $ λm, m.update ⟨"k", by rw h₂; exact v[0]⟩ (eq.mpr (show _ = ℕ, from begin unfold parlang_mcl_tlocal, simp, unfold signature.lean_type_of lean_type_of, rw h₁, end) 0)) ac₁ n₂ 
(s₂.map_active_threads ac₂ $ λts, ts.compute $ λm, m.update ⟨"k", by rw h₂; exact v[0]⟩ (eq.mpr (show _ = ℕ, from begin unfold parlang_mcl_tlocal, simp, unfold signature.lean_type_of lean_type_of, rw h₁, end) 0)) ac₂)
    k₁ k₂ 
  (λn₁ s₁ ac₁ n₂ s₂ ac₂, ∃ m₁ m₂, s₁.syncable m₁ ∧ s₂.syncable m₂ ∧ Q m₁ m₂)) :
rhl.mclp_rel eq 
(mclp.intro (λ m, e₁) (
    @mclk.tlocal_assign sig type.int _ "k" v[literal_int 0 rfl] h₁ h₂ read_tid ;;
    k₁
))
(mclp.intro (λ m, e₂) (
    mclk.for "k" h₁ h₂ read_tid ((@tlocal_var sig _ _ "k" (λ_, 0) h₁ h₂ h₃) < literal_int e₂ rfl) (mclk.tlocal_assign "k" v[0] h₁ h₂ $ tlocal_var "k" (λ_, 0) h₁ h₂ h₃ + literal_int e₂ rfl)
        k₂
)) Q := begin
    apply rhl.rel_mclk_to_mclp,
    intros n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ hp he₁,
    cases hp with m₁ hp,
    cases hp with m₂ hp,
    specialize h n₁ n₂ (state.map_active_threads ac₁ (thread_state.compute $ λm, m.update ⟨"k", by rw h₂; exact v[0]⟩ (eq.mpr _ $ m.get ⟨"tid", begin rw sig.property.right.left, exact v[0], end⟩)) s₁) s₁' s₂ ac₁ ac₂,
    swap 2, {
        unfold parlang_mcl_tlocal signature.lean_type_of lean_type_of,
        rw h₁,
        rw sig.property.left,
    },
    specialize h _,
    swap 2,
    {
        use m₁,
        use m₂,
        unfold initial_kernel_assertion,
        unfold initial_kernel_assertion at hp,
        delta thread_state.compute,
        rw ← state.syncable_tlocal,
        rw ← state.syncable_tlocal,
        rw ← state.syncable_tlocal,
        split, {
            exact hp.left,
        },
        split, {
            exact hp.right.left,
        },
        split, {
            exact hp.right.right.left,
        },
        split, {
            exact hp.right.right.right.left,
        },
        split, {
            intros i,
            have : vector.nth ac₁ i = tt := sorry,
            simp only [state.map_active_threads_nth_ac this],
            rw memory.update_update_eq,
            rw hp.right.right.right.right.left i,
            simp [mcl_init],
            funext i,
            cases i,
            by_cases a : i_fst = "k",
            {
                subst a,
                sorry,
            },
            sorry,
        },
        sorry,
    },
    sorry,
    sorry,
end

example : rhl.mclp_rel eq p₁ p₂ eq := begin 
    sorry,
    -- apply main transformation rule
end

end coarsening