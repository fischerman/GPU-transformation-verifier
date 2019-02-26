import data.vector

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

protected def mem {α : Type} {n : ℕ} : α → vector α n → Prop
| a v := a ∈ v.to_list

instance {α : Type} {n : ℕ} : has_mem α (vector α n) :=
⟨vector.mem⟩

set_option trace.eqn_compiler.elim_match true

lemma nat_le_zero {n : ℕ} : n < 0 → false := by sorry

-- lemma da {α} {n} {tl : list α} {a hd : α} {h : tl.length = n} : a ∈ (⟨tl, h⟩ : vector α n) → a ∈ (⟨hd :: tl, h⟩ : vector α n)

lemma contains_nth {α : Type} {n : ℕ} {v : vector α n} {i : fin n} : (v.nth i) ∈ v := begin
    induction n,
    case nat.zero {
        cases i,
        apply false.elim,
        apply nat_le_zero i_is_lt,
    },
    case nat.succ {
        --rw ← cons_head_tail v,
        cases i,
        cases v,
        cases v_val,
        case list.nil {
            sorry -- contr
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

            }
        }
    }
end

--     have : ¬(0 < 0) := by sorry,
--     cases i,
--     induction i_val,
--     case nat.zero {
--         cases n,
--         case nat.zero {
--             contradiction,
--         },
--         case nat.succ {
--             cases v,
--             cases v_val,
--             case list.nil {
--                 rw ← v_property at i_is_lt,
--                 simp at i_is_lt,
--                 contradiction,
--             },
--             case list.cons {
--                 rw nth,
--                 simp,
--                 sorry, -- should be trivial but how to unfold ∈?
--             },
--         }
--     },
--     case nat.succ {
--         -- index is either i_val_n + 1 or below
--         cases v,
--         cases v_val,
--         case list.nil {
--             sorry -- proof by contr.
--         },
--         case list.cons {
--             rw nth,
--             rw list.nth_le,
--             have : i_val_n < n := by sorry,
--             specialize i_val_ih this,
--             rw nth at i_val_ih,
--             rw list.nth_le at i_val_ih,
--         }
--     }
-- end

-- begin
--   have h_hdtl : ∃ x xs, s.threads = (x :: xs) := begin
--     apply list_aux.list_length_neq_zero,
--     apply nat_aux.lt_neq_zeor t,
--     assumption,
--   end,
--   cases h_hdtl with ts' h_hdtl,
--   cases h_hdtl with tail heq,
--   induction t,
--   case nat.zero {
--     have : ts = ts' := begin
--       rw ← h,
--       rw heq at hl,
--       rw th,
--       sorry,
--     end,
--     rw this,
--     rw heq,
--     simp,
--   },
--   case nat.succ {
--     by_cases hleq : t_n < list.length (s.threads),
--     {
--       apply t_ih hleq,
--       assumption,
--     }, {

--     }
--   }
-- end

end vector