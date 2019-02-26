import data.vector

universes u v w

namespace list_aux

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

end list_aux

namespace nat_aux

lemma lt_neq_zeor (n m : ℕ) : n < m → m ≠ 0 := begin
    intro,
    intro b,
    rw b at a,
    cases a,
end

end nat_aux

namespace set_aux

lemma union_no_mem_left {α : Type} {a : α} {b c : set α} (h : a ∉ b ∪ c) : a ∉ b := sorry

end set_aux

namespace vector

protected def mem {α : Type u} {n : ℕ} : α → vector α n → Prop
| a v := a ∈ v.to_list

instance {α : Type u} {n : ℕ} : has_mem α (vector α n) :=
⟨vector.mem⟩

lemma nat_le_zero {n : ℕ} : n < 0 → false := by sorry

lemma mem_elim_head {α : Type u} {n} {tl : list α} {a hd : α} (h) : 
a ∈ (show vector α n, from ⟨tl, h⟩) → a ∈ (show vector α (nat.succ n), from ⟨hd :: tl, congr_arg nat.succ h⟩) := sorry

lemma contains_nth {α : Type} {n : ℕ} {v : vector α n} {i : fin n} : (v.nth i) ∈ v := begin
    induction n,
    case nat.zero {
        cases i,
        apply false.elim,
        apply nat_le_zero i_is_lt,
    },
    case nat.succ {
        cases i,
        cases v,
        cases v_val,
        case list.nil {
            rw list.length at v_property,
            contradiction,
        },
        case list.cons {
            cases i_val,
            case nat.zero {
                rw nth,
                simp, -- should be trivial but how to unfold ∈?
                sorry,
            },
            case nat.succ {
                rw nth,
                simp,
                have: list.length v_val_tl = n_n := begin 
                    apply nat.succ_inj,
                    rw list.length at v_property,
                    assumption,
                end,
                apply mem_elim_head this,
                specialize @n_ih (⟨v_val_tl, this⟩),
                have val_lt_n : i_val < n_n := by apply nat.lt_of_succ_lt_succ i_is_lt,
                specialize @n_ih ⟨i_val, val_lt_n⟩,
                rw nth at n_ih,
                simp at n_ih,
                assumption,
            }
        }
    }
end

end vector