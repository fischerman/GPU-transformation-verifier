import mcl
import mcl_rhl
import parlang
open mcl
open mcl.mclk
open mcl.rhl

namespace assign_mcl

def sigc : signature_core
| "tid" := { scope := scope.tlocal, type := ⟨1, type.int⟩ }
| _ := { scope := scope.global, type := ⟨1, type.int⟩ }

def sig : signature := ⟨sigc, begin
    split,
    refl,
    refl,
end⟩

lemma a_is_global : is_global (sig.val "a") := by apply eq.refl
lemma tid_is_tlocal : is_tlocal (sig.val "tid") := by apply eq.refl

-- TODO generate those proofs directly from signature
-- make type classes out of those
-- make name explicit in state.update
def read_tid := (expression.tlocal_var "tid" (λ_, 0) (show type_of (sig.val "tid") = type.int, by apply eq.refl) (show (sig.val "tid").type.dim = 1, by apply eq.refl) tid_is_tlocal)

instance : has_one (expression sig (type_of (sig.val "b"))) := begin
    have : type_of (sig.val "b") = type.int := by apply eq.refl,
    rw this,
    apply_instance,
end

def p₁ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "a" v[read_tid] (by refl) (by refl) read_tid ;;
    mclk.global_assign "b" v[read_tid] (by refl) (by refl) (read_tid + (expression.literal_int 1 (by refl)))
)

def p₂ : mclp sig := mclp.intro (λ m, 100) (
    mclk.global_assign "b" v[read_tid] (by refl) (by refl) (read_tid + (expression.literal_int 1 (by refl))) ;;
    mclk.global_assign "a" v[read_tid] (by refl) (by refl) read_tid
)

open parlang
open parlang.state
open parlang.thread_state

--#reduce update_global_vars_for_expr (read_tid + 1)

--set_option pp.implicit true

#print p₁._proof_1

-- lemma store_get_update (n) {idx : list ℕ} {sig : signature} {dim} {idx₁ : vector ℕ dim} {idx₂ : vector ℕ dim} {h : type_of (sig n) = signature.type_of n sig} {h' v} (hidx : idx₁.to_list = idx₂.to_list) : 
--     @store _ _ (parlang_mcl_global sig) _ (λ (s : memory $ parlang_mcl_tlocal sig), ⟨⟨n, idx⟩, @state.get' sig (sig.type_of n) n dim idx₁ h h' (@state.update' sig (sig.type_of n) n dim idx₂ h h' v s)⟩) = 
--     store (λ (s : mcl.state sig), ⟨(n, idx), v⟩) := begin
--     sorry
-- end

-- lemma store_get_update' (n₁ n₂) {sig : signature} {dim₁ dim₂} {idx} {idx₁ : vector ℕ dim₁} {idx₂ : vector ℕ dim₂} {h₁ h₁' h₂ h₂' v} 
--     (hn : n₁ = n₂) (hidx : idx₁.to_list = idx₂.to_list) (ht : type_map (sig.type_of n₁) = type_map (sig.type_of n₂)) : 
--     @store _ _ (parlang_mcl_global sig) _ (λ (s : mcl.state sig), ⟨(n₁, idx), @state.get' sig (sig.type_of n₁) n₁ dim₁ idx₁  h₁ h₁' (@state.update' sig (sig.type_of n₂) n₂ dim₂ idx₂ h₂ h₂' v s)⟩) = 
--     store (λ (s : mcl.state sig), ⟨(n₁, idx), (show (type_map $ sig.type_of n₁), begin rw ht, exact v end)⟩) := begin
--     sorry
-- end

--list.all (vector.to_list ?m_4) (bnot ∘ expr_reads ?m_5)

lemma vector_map_single {s : memory $ parlang_mcl_tlocal sig} {t} {expr : expression sig t} : vector.map (eval s) v[expr] = v[eval s expr] := begin
    refl,
end

lemma lt_zero_one : 0 < 1 := by sorry

def compute_list {σ ι : Type} {τ : ι → Type} [decidable_eq ι] : list (σ → σ) → (thread_state σ τ → thread_state σ τ)
| (f :: tl) := compute_list tl ∘ @compute σ ι τ _ f
| [] := id

lemma compute_to_compute_list {σ ι : Type} {τ : ι → Type} [decidable_eq ι] (f : σ → σ) : @compute σ ι τ _ f = compute_list [f] := by refl

lemma compute_list_merge {σ ι : Type} {τ : ι → Type} [decidable_eq ι] (f g : list (σ → σ)) : 
(@compute_list σ ι τ _ g) ∘ compute_list f = compute_list (f ++ g) := begin
    induction f,
    case list.nil {
        simp [compute_list],
    }, {
        simp [compute_list],
        rw ← f_ih,
    }
end

lemma store_access_elim_name {sig : signature} {n n_idx} {s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} {var} {idx : vector (expression sig type.int) n_idx} 
{t h₄} {h₃ : type_of (sig.val var) = t } {f} {t : fin n} {i} {ac₁ : vector bool n} {updates}
(h₁ : i ∉ accesses (vector.nth ((map_active_threads ac₁ (f ∘ compute_list updates) s).threads) t)) 
(h₂ : i.1 ≠ var) :
i ∉ accesses (vector.nth ((map_active_threads ac₁ (f ∘ (mcl_store var idx h₃ h₄) ∘ compute_list updates) s).threads) t) := begin
    sorry,
end


lemma store_access_elim_idx {sig : signature} {n n_idx} {s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} {var} {idx : vector (expression sig type.int) n_idx} 
{t} {h₄ : ((sig.val var).type).dim = n_idx} {h₃ : type_of (sig.val var) = t } {f} {t : fin n} {i : mcl_address sig} {ac₁ : vector bool n} {updates}
(h₂ : i.2.to_list ≠ (idx.map ((eval (((map_active_threads ac₁ (compute_list updates) s).threads).nth t).tlocal))).to_list) 
(h₁ : i ∉ accesses (vector.nth ((map_active_threads ac₁ (f ∘ compute_list updates) s).threads) t)) :
i ∉ accesses (vector.nth ((map_active_threads ac₁ (f ∘ (mcl_store var idx h₃ h₄) ∘ compute_list updates) s).threads) t) := begin
    sorry,
end

lemma store_access_elim_idx' {sig : signature} {n n_idx} {s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} {var} {idx : vector (expression sig type.int) n_idx} 
{t} {h₄ : ((sig.val var).type).dim = n_idx} {h₃ : type_of (sig.val var) = t } {t : fin n} {i : mcl_address sig} {ac₁ : vector bool n} {updates}
(h₂ : i.2.to_list ≠ (idx.map ((eval (((map_active_threads ac₁ (compute_list updates) s).threads).nth t).tlocal ))).to_list) 
(h₁ : i ∉ accesses (vector.nth (s.threads) t)) :
i ∉ accesses (vector.nth ((map_active_threads ac₁ ((mcl_store var idx h₃ h₄) ∘ compute_list updates) s).threads) t) := begin
    sorry,
end

lemma store_store_success {sig : signature} {i : mcl_address sig} {updates} {ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} 
{dim} {idx : vector (expression sig type.int) dim} {var t} {h₁ : type_of (sig.val var) = t} {h₂ : ((sig.val var).type).dim = dim} 
{f : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} : 
i = ⟨var, vector_mpr h₂ (idx.map (eval (compute_list updates ts).tlocal))⟩ → i ∈ ((f ∘ mcl_store var idx h₁ h₂ ∘ compute_list updates) ts).stores := by sorry

lemma access_init  {sig₁ sig₂ : signature} {P : memory (parlang_mcl_global sig₁) → memory (parlang_mcl_global sig₂) → Prop} 
{f₁ : memory (parlang_mcl_global sig₁) → ℕ} {f₂ : memory (parlang_mcl_global sig₂) → ℕ} {m₁ : memory (parlang_mcl_global sig₁)} {m₂ : memory (parlang_mcl_global sig₂)} 
{n₁} {s₁ : state n₁ (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig₁)} {ac₁ : vector bool n₁} {n₂} {s₂ : state n₂ (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig₂)} {ac₂ : vector bool n₂} {t} {i} : 
initial_kernel_assertion mcl_init mcl_init P f₁ f₂ m₁ m₂ n₁ s₁ ac₁ n₂ s₂ ac₂ → i ∉ accesses (vector.nth (s₁.threads) t) := begin
    sorry
end

lemma list_neq_elem {α : Type} {l l' : list α} (n : ℕ) (h : n < l.length) (h' : n < l'.length) : l.nth_le n h ≠ l'.nth_le n h' → l ≠ l' := by sorry

lemma list_nth_vector {α l} {v : vector α l} {n h} : list.nth_le (vector.to_list v) n h = v.nth ⟨n, (by sorry)⟩ := by sorry

lemma list_one_eq {α : Type} {l₁ l₂ : list α} (h : l₁.length = 1) : ([l₁.nth_le 0 (by rw h; exact lt_zero_one)] : list α) = l₂ → l₁ = l₂ := sorry

set_option trace.simplify.rewrite true 

variable (m''' : memory (parlang_mcl_global sig))

set_option trace.check true

-- question: should we limit ourselfs to global scope here?
structure array_access (sig : signature) (var : string) (i : mcl_address sig) : Prop :=
(var_eq : i.1 = var)
(idx_len : i.2.length = (sig.val var).type.dim)
-- (bound : list.forall₂ nat.lt i.2 (sig var).type.sizes.to_list)

structure array_access_tid_to_idx (sig : signature) (var : string) (i : mcl_address sig) (n : ℕ) extends array_access sig var i : Prop :=
(one_dim : i.2.length = 1)
(field_per_thread : i.2.nth ⟨0, begin rw [var_eq, ←idx_len, one_dim], exact lt_zero_one end⟩ < n)

-- todo: can also be fin
def array_access_tid_to_idx.tid_to_idx {sig : signature} {var : string} {i : mcl_address sig} {n} (a : array_access_tid_to_idx sig var i n) : 
fin n := ⟨i.2.nth ⟨0, begin rw [a.to_array_access.var_eq, ← a.to_array_access.idx_len, a.one_dim], exact lt_zero_one end⟩, a.field_per_thread⟩

instance forall₂_decidable {α : Type} [decidable_eq α] (l₁ : list α) (l₂ : list α) : decidable (list.forall₂ eq l₁ l₂) := begin
    induction l₁ generalizing l₂,
    case list.nil {
        cases l₂,
        case list.nil {
            exact is_true (list.forall₂.nil)
        },
        case list.cons {
            exact is_false (begin
                intro h,
                cases h,
            end)
        }
    },
    case list.cons {
        cases l₂,
        case list.nil {
            exact is_false (begin
                intro h,
                cases h,
            end)
        },
        case list.cons {
            specialize l₁_ih l₂_tl,
            admit,
            -- by_cases h : l₁_hd = l₂_hd ∧ list.forall₂ eq l₁_tl l₂_tl,
            -- {
            --     exact is_true (begin
            --         apply list.forall₂.cons,
            --         exact h,
            --         apply l₁_ih,
            --     end)
            -- }
        }
    }
end

instance {sig var i} : decidable (array_access sig var i) :=
  if var_eq : i.1 = var then
    if idx_len : i.2.length = (sig.val var).type.dim then is_true ⟨var_eq, idx_len⟩
    --   if bound : list.forall₂ eq i.2 (sig var).type.sizes.to_list then is_true ⟨var_eq, idx_len, bound⟩
    --   else is_false (assume h : array_access sig var i, bound (array_access.bound h))
    else is_false (assume h : array_access sig var i, idx_len (array_access.idx_len h))
  else is_false (assume h : array_access sig var i, var_eq (array_access.var_eq h))

instance ll {sig var i n} : decidable (array_access_tid_to_idx sig var i n) := sorry

lemma store_global_success {sig : signature} {i : mcl_address sig} {updates} 
{dim} {idx : vector (expression sig type.int) dim} {var₁ var₂ t} {h₁ : type_of (sig.val var₂) = t} {h₂}
{ts : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)}
{f : thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig) → thread_state (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} (a : array_access sig var₁ i) (h : var₁ = var₂) : ((
        f ∘
        mcl_store var₂ idx h₁ h₂ ∘
        compute_list updates)
    ts
).global i = (begin simp [parlang_mcl_global, signature.lean_type_of, lean_type_of], rw a.var_eq, rw h, exact ((compute_list updates ts).tlocal.get ⟨var₂, vector_mpr h₂ $ idx.map (eval (compute_list updates ts).tlocal)⟩) end) := sorry

def memory_array_update_tid {sig : signature} {n} (var) (s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)) (expr : expression sig (type_of (sig.val var))) (m : memory (parlang_mcl_global sig)) := 
((list.range_fin n).foldl (λ (m : parlang.memory (parlang_mcl_global sig)) i, m.update ⟨var, eq.mpr sorry v[i]⟩ (eval (s.threads.nth i).tlocal expr))) m

lemma memory_array_update_tid_skip {sig : signature} {n} {var₁ var₂} {s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} 
{expr : expression sig (type_of (sig.val var₂))} {m : memory (parlang_mcl_global sig)} {i} (a : array_access sig var₁ i) (h : var₁ ≠ var₂) : 
(memory_array_update_tid var₂ s expr m) i = m i := begin
    cases i,
    have : i_fst = var₁ := a.var_eq,
    admit,
    -- induction on n
    -- show non-interference on memory.update
end

lemma memory_array_update_tid_success {sig : signature} {n} {var₁ var₂} {s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_global sig)} 
{expr : expression sig (type_of (sig.val var₂))} {m : memory (parlang_mcl_global sig)} {i} (a : array_access_tid_to_idx sig var₁ i n) (h : var₁ = var₂) : 
(memory_array_update_tid var₂ s expr m) i = eval (s.threads.nth ⟨_, a.field_per_thread⟩).tlocal (by rw a.to_array_access.var_eq; rw h; exact expr) := begin
    admit,
end

-- #reduce eval ((compute_list [/- λ (s : state sig), state.update' p₁._proof_1 _ (eval s read_tid) s -/] {tlocal := mcl_init 9, global := m''', loads := ∅, stores := ∅}).tlocal) (vector.nth [read_tid] ⟨0, lt_zero_one⟩)

universe u
lemma hh {a b : Sort u} (h : a == b) : a = b := begin
    cases h,
    refl,
end

lemma hhh {α : Type} (h: α = α) (a b : α) : (a = eq.mpr h b) = (a = b) := by refl
lemma hhh' {α : Type} (h: α = α) (a : α) : eq.mpr h a = a := by refl

--set_option pp.implicit true

#print p₁._proof_2

#reduce eval (mcl_init 0) read_tid
#check eval (mcl_init 0) read_tid = 0

variable (a : nat)

#check a = a

-- todo change the definition of syncable to take a fin
-- todo extend array_access_tid to contain the value as an expression

-- this approach is like computing both programs and comparing their output
-- this is a fairly naive approach, another approach would be to show that their behavior is equal (based on the fact that we have to show equality)
/--
Show 
-/
lemma assign_rel : mclp_rel eq p₁ p₂ eq := begin
    apply rel_mclk_to_mclp,

    apply skip_right.mpr,
    apply rhl.seq,
    swap,

    apply skip_left_after.mpr,
    apply skip_right.mpr,
    apply rhl.seq,
    swap,

    -- break it down into individual proofs
    apply add_skip_left.mpr,
    apply rhl.seq,
    swap,
    {
        apply global_assign_right,
    },{
        apply global_assign_right,
    }, {
        apply global_assign_left,
    },
    apply global_assign_left',
    intros _ _ _ _ _ _ h,
    cases h with m₁ h,
    cases h with m₂ h,
    simp,
    have : n₁ = n₂ := begin
        sorry
    end,
    subst this,
    have hseq : s₁ = s₂ := begin
        sorry
    end,

    -- the proof obligation in the form of a map thread on syncable is the simple version because we never consider threads to change active state (here all threads are always active)

    -- the two updates store indepedently because "a" ≠ "b"
    -- the two updates read indepedently because they both depend on the same state (AFAIK they could still be swaped because the state is fixed)
    apply exists.intro (memory_array_update_tid "b" s₁ (read_tid + (expression.literal_int 1 (by refl))) (memory_array_update_tid "a" s₁ read_tid m₁)),

    split, {
        have : update_global_vars_for_expr read_tid = id := by refl,
        rw this,
        have : update_global_vars_for_expr (read_tid + (expression.literal_int 1 (show type_of (sig.val "b") = type_of (sig.val "b"), by refl))) = id := by refl,
        rw this,
        simp,

        -- put maps in store
        -- todo we could distinct cases
           -- store stores the same value as update
           -- update changes the value of an index of store
           -- update can be ignored
        -- rw ← function.comp.assoc,
        -- rw ← function.comp.assoc,
        -- rw thread_state_map,
        -- rw ← function.comp.assoc,
        -- rw thread_state_map',
        -- rw function.comp.assoc,
        -- rw function.comp.assoc,
        -- rw syncable_remove_map,

        have hbni : list.all (vector.to_list v[read_tid]) (bnot ∘ expr_reads "b") = tt := by refl,
        have hani : list.all (vector.to_list v[read_tid]) (bnot ∘ expr_reads "a") = tt := by refl,
        have hani' : expr_reads "a" read_tid = ff := by refl,
        have hbni' : expr_reads "b" read_tid = ff := by refl,
        have hbni'' : expr_reads "b" (read_tid + expression.literal_int 1 p₁._proof_5) = ff := by refl,
        have hani'' : expr_reads "a" (read_tid + expression.literal_int 1 p₁._proof_5) = ff := by refl,

        -- resolve get and update (the result should only be mcl_init, literals and memory (in case of loads))

        -- simp [state_get_update_success _ _ _ _ _, eval_update_ignore' hbni, eval_update_ignore' hani, eval_update_ignore hani'', eval_update_ignore hbni''],
        -- conv {
        --     congr,
        --     congr,
        --     skip,
        --     congr,
        --     congr,
        --     funext,
        --     rw vector_map_single,
        --     rw vector.to_list,
        --     rw eval_update_ignore hbni',
        --     rw eval_update_ignore hani',
        --     skip,
        --     congr,
        --     funext,
        --     rw vector_map_single,
        --     rw vector.to_list,
        --     rw eval_update_ignore hani',
        -- },
        intro,
        by_cases ha : array_access_tid_to_idx sig "a" i n₁,
        {
            right,
            use ha.tid_to_idx,
            repeat { rw compute_to_compute_list },
            split,
            {
                -- find the correct store instruction which performs the write
                rw map_active_threads_nth_ac, {
                    rw initial_kernel_assertion_left_thread_state h,
                    apply store_store_success,
                    apply address_eq,
                    swap,
                    {
                        apply ha.var_eq,
                    }, {
                        rw vector_map_single,
                        cases i,
                        cases ha,
                        cases ha__to_array_access,
                        simp at ha__to_array_access_var_eq,
                        simp at ha__to_array_access_idx_len,
                        dedup,
                        subst ha__to_array_access_var_eq_1,
                        apply vector.eq_one,
                        refl,
                    }
                }, {
                    -- thread is active
                    apply all_threads_active_nth,
                    exact h.left_all_threads_active,
                }
            }, {
                split,
                {
                    rw map_active_threads_nth_ac (all_threads_active_nth h.left_all_threads_active _),
                    rw memory_array_update_tid_skip ha.to_array_access,
                    swap, {
                        intro heq,
                        cases heq,
                    },
                    rw memory_array_update_tid_success ha,
                    swap, {
                        refl,
                    },
                    rw store_global_success ha.to_array_access,
                    swap, {
                        refl
                    },
                    rw initial_kernel_assertion_left_thread_state h,
                    sorry, -- proof that the value is the same
                }, {
                    intros t' hneqtt',
                    apply store_access_elim_idx, {
                        apply list_neq_elem 0, 
                        swap, {
                            rw vector.length_list,
                            rw ha.one_dim,
                            exact lt_zero_one,
                        }, {
                            rw list_nth_vector,
                            rw list_nth_vector,
                            rw vector.nth_map,
                            rw map_active_threads_nth_ac,
                            rw initial_kernel_assertion_left_thread_state h,
                            exact fin.fin_eq hneqtt',
                            sorry, -- todo thread is actives
                        }, {
                            rw vector.length_list,
                            rw vector.length,
                            exact lt_zero_one,
                        }
                    }, {
                        rw function.comp.assoc,
                        rw compute_list_merge,
                        apply store_access_elim_idx', {
                            apply list_neq_elem 0, 
                            swap, {
                                rw vector.length_list,
                                rw ha.one_dim,
                                exact lt_zero_one,
                            }, {
                                rw list_nth_vector,
                                rw list_nth_vector,
                                rw vector.nth_map,
                                rw map_active_threads_nth_ac,
                                rw initial_kernel_assertion_left_thread_state h,
                                exact fin.fin_eq hneqtt',
                                sorry, -- todo thread is actives
                            }, {
                                sorry, -- todo prove length through map and stuff
                            }
                        }, {
                            -- initial state does not access any i
                            apply access_init h,
                        }
                    }
                }
            },
        }, {
            sorry,
        }
    }, {
        sorry,
    }
end

end assign_mcl