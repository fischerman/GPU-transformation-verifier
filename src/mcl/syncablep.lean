import mcl.defs
import mcl.rhl
import mcl.lemmas
import mcl.compute_list
import mcl.ts_updates
import syncablep

open parlang
open parlang.thread_state
open parlang.state
open mcl
open mcl.rhl

/-- Copies *var* from tlocal of the nth thread into index n of *m* (forall n). Generally used as an assertion language for Hoare proofs -/
def from_tlocal {sig : signature} {n} (var) (s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)) (m : memory (parlang_mcl_shared sig)) (h : (((sig.val var).type).dim) = 1) := 
((list.range_fin n).foldl (λ (m : parlang.memory (parlang_mcl_shared sig)) tid, 
    m.update ⟨var, eq.mpr (by rw h) v[tid.val]⟩ ((s.threads.nth tid).tlocal.get ⟨var, eq.mpr (by rw h) v[tid.val]⟩))) m

lemma from_tlocal_comm_update {sig : signature} {n} (var₁ var₂) (s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig))
(m : memory (parlang_mcl_shared sig)) {h₁} {idx val} :
from_tlocal var₁ s (m.update ⟨var₂, idx⟩ val) h₁ = memory.update (from_tlocal var₁ s m h₁) ⟨var₂, idx⟩ val := begin
    unfold from_tlocal,
    induction n,
    { refl, },
    {
        rw [list.foldl_range_fin_succ],
        sorry, -- complicated with dependent type fin
    }
end

lemma from_tlocal_comm {sig : signature} {n} (var₁ var₂) (s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig))
(s' : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)) (m : memory (parlang_mcl_shared sig)) {h₁ h₂} :
from_tlocal var₁ s (from_tlocal var₂ s' m h₂) h₁ = from_tlocal var₂ s' (from_tlocal var₁ s m h₁) h₂ := begin
    unfold from_tlocal,
    induction n,
    {
        refl,
    }, {
        rw [list.foldl_range_fin_succ],
        rw [list.foldl_range_fin_succ],
        repeat { rw ← from_tlocal },
        sorry,
    }
end

--lemma : from_tlocal "b" (map_active_threads ac (ts_updates [op.compute_list (... :: coms)]) s = from_tlocal "b" (map_active_threads ac (ts_updates [op.compute_list (... :: coms)]) s

lemma from_tlocal_eq {sig : signature} {n}
{s s' : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)}
{m m' : memory (parlang_mcl_shared sig)} {var} {h : ((sig.val var).type).dim = 1} :
(∀ tid, (s.threads.nth tid).tlocal.get ⟨var, begin rw h, exact v[tid] end⟩ = (s'.threads.nth tid).tlocal.get ⟨var, begin rw h, exact v[tid] end⟩) →
m = m' →
from_tlocal var s m h = from_tlocal var s' m' h := begin
    intros hveq hmeq,
    subst hmeq,
    unfold from_tlocal,
    induction n,
    { refl, },
    {
        rw list.foldl_range_fin_succ,
        sorry,
    }
end

lemma syncable'_compute_list_syncable {sig : signature} {n} {ac : vector bool n} {computes} {shole lhole : set $ mcl_address sig}
{s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)}
{m : memory (parlang_mcl_shared sig)} : 
s.syncable m →
(∀ tid : fin n, (s.threads.nth tid).stores = ∅) →
(∀ tid : fin n, (s.threads.nth tid).loads = ∅) →
syncable' shole lhole (map_active_threads ac (ts_updates [op.compute_list computes]) s) m := begin
    intros syncable no_stores no_loads,
    unfold syncable' state.syncable,
    split,
    {
        simp only [accesses, compute_list_stores', compute_list_loads', compute_list_shared'],
        exact syncable,
    }, {
        intros i tid,
        simp [no_stores tid, no_loads tid],
    }
end

instance deciable_exists_nat (p) : decidable (@Exists ℕ p) := sorry
instance deciable_exists_fin (n p) : decidable (@Exists (fin n) p) := sorry


/-- Processes a store
Which thread accesses which index doesn't matter 
-/
lemma syncable'_store {sig : signature} {n} {ac : vector bool n} {computes} {shole lhole : set $ mcl_address sig}
{dim} {idx : vector (expression sig type.int) dim} {var t} {h₁ : type_of (sig.val var) = t} {h₂}
{updates : list $ op sig}
{s : state n (memory $ parlang_mcl_tlocal sig) (parlang_mcl_shared sig)}
{m : memory (parlang_mcl_shared sig)} 
(idx_1 : (((sig.val var).type).dim) = 1) : 
(∀ idx, (⟨var, idx⟩ : mcl_address sig) ∉ shole) →
(∀ idx, (⟨var, idx⟩ : mcl_address sig) ∉ lhole) →
(∀ tid₁ tid₂, tid₁ ≠ tid₂ → idx.map (λ ind, eval (s.threads.nth tid₁).tlocal ind) ≠ idx.map (λ ind, eval (s.threads.nth tid₂).tlocal ind)) →
syncable' (shole ∪ array_address_range var) (lhole ∪ array_address_range var) (map_active_threads ac (ts_updates $ op.compute_list computes :: updates) s) m →
syncable' shole lhole (map_active_threads ac (ts_updates $ op.compute_list computes :: op.store var idx h₁ h₂ :: updates) s) (from_tlocal var (map_active_threads ac (ts_updates [op.compute_list computes]) s) m idx_1)
| var_not_in_shole var_not_in_lhole distinct_idx (and.intro syncable holes_constraint) := begin
    clear syncable'_store,
    unfold syncable',
    -- proof: syncable
    split, {
        intros i,
        by_cases i_is_var : i.fst = var,
        {
            subst i_is_var,
            specialize var_not_in_shole i.snd,
            specialize var_not_in_lhole i.snd,
            -- cases distinct out-of-bound
            -- by_cases i_is_oob : (∃ (tid : fin n), i.snd = eq.mpr _ (idx.map (λ ind, eval (s.threads.nth tid).tlocal ind))),
            sorry,
        },
        sorry,
    }, {
        -- proof: store hole
        intros i tid,
        have : i ∈ shole ∪ array_address_range var := sorry, --trivial
        
        by_cases i_is_var : i.fst = var,
        {
            -- if i is var we store into hole -> contradiction
            subst i_is_var,
            specialize var_not_in_shole i.snd,
            specialize var_not_in_lhole i.snd,
            cases i,
            split,
            {
                intros i_in_store,
                contradiction,
            }, {
                intros i_in_loads,
                contradiction,
            }
        }, {
            by_cases tid_activeness : ac.nth tid = tt,
            {
                rw map_active_threads_nth_ac tid_activeness,
                specialize holes_constraint i tid,
                
                rw map_active_threads_nth_ac tid_activeness at holes_constraint,
                rw [ts_updates] at holes_constraint,
                /- LARGE PROOF STARTS HERE -/
                clear syncable,
                rw [ts_updates, ts_updates],
                revert holes_constraint,
                generalize eq : compute_list computes (vector.nth (s.threads) tid) = s',
                rw ← list.reverse_reverse updates,
                generalize eq' : list.reverse updates = ups,
                intro holes_constraint,
                -- we do induction on the reverse of the list, such that we "append" elements to the end of updates (i.e. later)
                -- afterwards cases on the update (either store or compute)
                induction ups generalizing updates,
                {
                    simp [ts_updates, thread_state.tlocal_to_shared, store],
                    simp [ts_updates, thread_state.tlocal_to_shared, store] at holes_constraint,
                    cases holes_constraint with shole_constraint lhole_constraint,
                    split, {
                        intros i_in_shole i_in_stores,
                        cases i_in_stores, {
                            subst i_in_stores,
                            apply i_is_var,
                            refl,
                        }, {
                            specialize shole_constraint (or.inl i_in_shole),
                            contradiction,
                        },
                    }, {
                        intro i_in_lhole,
                        apply lhole_constraint (or.inl i_in_lhole),
                    }
                }, {
                    rw [ts_update_split],
                    simp,
                    cases ups_hd,
                    {
                        simp only [ts_updates],
                        simp only [ts_update_split] at holes_constraint,
                        simp [ts_updates, -set.mem_union_eq] at holes_constraint,
                        specialize @ups_ih _ (list.reverse ups_tl),
                        swap,
                        {
                            split, {
                                intro,
                                apply store_stores,
                                apply holes_constraint.left a,
                            }, {
                                intro,
                                apply store_loads,
                                apply holes_constraint.right a,
                            },
                        },
                        simp [thread_state.tlocal_to_shared, store],
                        simp [thread_state.tlocal_to_shared, store] at ups_ih,
                        split,
                        {
                            intros i_in_shole,
                            rw not_or_distrib,
                            split, {
                                -- proof that the new store doesn't store in i
                                cases holes_constraint with shole_constraint lhole_constraint,
                                simp [thread_state.tlocal_to_shared, store] at shole_constraint,
                                rw not_or_distrib at shole_constraint,
                                cases shole_constraint (or.inl i_in_shole),
                                rw ts_updates_tlocal s'.shared s'.loads s'.stores,
                                simp,
                                have : s' = {tlocal := s'.tlocal, shared := s'.shared, loads := s'.loads, stores := s'.stores} := begin
                                    cases s',
                                    simp,
                                end,
                                rw ← this,
                                assumption,
                            }, {
                                apply ups_ih.left i_in_shole,
                            }
                        }, {
                            intros i_in_lhole,
                            apply ups_ih.right i_in_lhole,
                        }
                    }, {
                        -- the head element is compute_list
                        simp [ts_updates],
                        apply ups_ih,
                        swap 3,
                        exact list.reverse ups_tl,
                        rw [ts_update_split] at holes_constraint,
                        simp [ts_updates] at holes_constraint,
                        simp,
                        exact holes_constraint,
                        simp,
                    }
                },
            }, {
                specialize holes_constraint i tid,
                rw ← map_active_threads_nth_inac tid_activeness,
                rw ← map_active_threads_nth_inac tid_activeness at holes_constraint,
                simp *,
                intro a,
                apply holes_constraint.right (or.inl a),
            }
        }
    },
end