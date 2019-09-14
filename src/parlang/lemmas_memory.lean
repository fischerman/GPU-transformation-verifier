import parlang.defs

namespace parlang
namespace memory

variables {ι : Type} {τ : ι → Type} [decidable_eq ι] {m : memory τ} {i i' : ι} {val val' : τ i}

lemma get_update_success : get (update m i val) i = val := begin
    unfold update get function.update,
    simp,
end

lemma get_update_skip (h : i' ≠ i) : get (update m i val) i' = get m i' := begin
    unfold update get function.update,
    simp [h],
end

lemma update_update_eq : update (update m i val) i val' = update m i val' := begin
    funext i',
    by_cases h : i' = i,
    simp [update, function.update, h],
    simp [update, function.update, h],
end

end memory
end parlang