

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
    assumption,
end