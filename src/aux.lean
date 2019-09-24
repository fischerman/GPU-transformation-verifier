import data.list.basic
import data.vector

universes u v w
variables {n : ℕ} {α β γ δ : Type}

notation `v[` v:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := v

@[simp]
lemma ite_else_ite {c} [decidable c] {b₁ b₂ b₃ :  Sort u} : ite c b₁ (ite c b₂ b₃) = ite c b₁ b₃ := begin
  by_cases c; simp *,
end

lemma lt_zero_one : 0 < 1 := nat.lt.base 0

@[simp]
lemma nat.succ_lt_succ_iff {n m : ℕ} : n + 1 < m + 1 ↔ n < m := nat.lt_succ_iff

lemma eq.mpr.intro {α : Type} (x : α) : eq.mpr rfl x = x := begin
  refl,
end

namespace fin

lemma fin_eq {f f' : fin n} : f ≠ f' → f.val ≠ f'.val := begin
  intro h,
  cases f,
  cases f',
  simp,
  intro h',
  apply h,
  subst h',
end

end fin

namespace list

lemma list_length_neq_zero {α} : ∀{l : list α}, l.length ≠ 0 → ∃ x xs, l = (x :: xs)
| []     h := (h rfl).elim
| (a::l) h := ⟨_, _, rfl⟩

lemma list_length_tail {α β : Type} {x : α} {y : β} {xs ys : list _}
  (h : (x :: xs).length = (y :: ys).length) : xs.length = ys.length :=
by simpa using h 

def range_fin_core (dim : ℕ) : Π n : ℕ, n <= dim → list (fin dim) → list (fin dim)
| 0 h l := l
| (nat.succ n) hs l := have h : n < dim := begin apply nat.succ_le_succ_iff.mp, apply nat.lt_succ_iff.mpr hs, end, range_fin_core n (le_of_lt h) (⟨n, h⟩ :: l)

def range_fin (n : ℕ) : list (fin n) :=
range_fin_core n n (by refl) []

-- TODO: we need something like list.range' for fin
--def range_fin' : ℕ → ℕ → list (fin n)

@[simp] lemma length_range_nth : length (range_fin n) = n := begin
  admit
end


def fin_inc : fin n → fin (nat.succ n)
| ⟨val, is_lt⟩ := ⟨val, nat.lt.step is_lt⟩

instance (n : ℕ) : has_coe (list (fin $ n)) (list (fin $ nat.succ n)) := ⟨map fin_inc⟩

lemma range_fin_succ : range_fin (nat.succ n) = ((range_fin n : list (fin n)) : list (fin $ nat.succ n)) ++ [⟨n, sorry⟩] := begin
  unfold range_fin,
  induction n, { refl, },
  {
    rw range_fin_core,
    sorry,
  }
end

lemma foldl_range_fin_succ {α : Type} {n : ℕ} (i : α) (r : α → fin (nat.succ n) → α) : foldl r i (range_fin (n + 1)) = r (foldl r i (range_fin n : list (fin n))) (nat.succ n) := begin
  induction n,
  { refl, },
  {
    rw [range_fin, range_fin_core],
    sorry,
  }
end

#print map₂._main

lemma map₂_map₂ (g : γ → β → δ) (f : α → β → γ) (l : list α) (l' : list β) : map₂ g (map₂ f l l') l' = map₂ (λ a b, g (f a b) b) l l' := begin
  induction l generalizing l',
  case list.nil { cases l'; refl, },
  case list.cons { cases l'; simp [map₂, *], }
end

lemma list_neq_elem {α : Type} {l l' : list α} (n : ℕ) (h : n < l.length) (h' : n < l'.length) : l.nth_le n h ≠ l'.nth_le n h' → l ≠ l' := by sorry

lemma list_nth_vector {α l} {v : vector α l} {n h} : list.nth_le (vector.to_list v) n h = v.nth ⟨n, (by sorry)⟩ := by sorry

lemma list_one_eq {α : Type} {l₁ l₂ : list α} (h : l₁.length = 1) : ([l₁.nth_le 0 (by rw h; exact lt_zero_one)] : list α) = l₂ → l₁ = l₂ := sorry

end list

namespace nat

lemma lt_neq_zeor (n m : ℕ) : n < m → m ≠ 0 := begin
    intro,
    intro b,
    rw b at a,
    cases a,
end

end nat

namespace set

lemma union_no_mem_left {α : Type} {a : α} {b c : set α} (h : a ∉ b ∪ c) : a ∉ b := sorry

end set

namespace vector

protected def mem {α : Type u} {n : ℕ} : α → vector α n → Prop
| a v := a ∈ v.to_list

instance {α : Type u} {n : ℕ} : has_mem α (vector α n) :=
⟨vector.mem⟩

lemma mem_def {α : Type*} {n : ℕ} (a : α) (v : vector α n) : a ∈ v ↔ a ∈ v.to_list :=
iff.rfl

lemma mem_nil {α : Type u} {a : α} : a ∉ (@vector.nil α) := by sorry

lemma nat_le_zero {n : ℕ} : n < 0 → false := by sorry

#check vector.cons

lemma mem_elim_head {α : Type u} {n} {tl : vector α n} {a hd : α} :
  a ∈ tl → a ∈ cons hd tl :=
sorry

lemma contains_nth {α : Type} : ∀{n : ℕ} {v : vector α n} {i : fin n}, (v.nth i) ∈ v
| n ⟨l, rfl⟩ ⟨i, hi⟩ :=
  begin
    dsimp only [vector.nth, vector.has_mem, vector.mem, to_list],
    rw list.mem_iff_nth_le,
    exact ⟨i, hi, rfl⟩
  end

lemma eq_element_wise {α : Type} : ∀{a b : vector α n}, (∀ i, a.nth i = b.nth i) → a = b 
:= begin
  -- TODO needs fixing
  intros a b hieq,
  apply vector.eq,
  cases a,
  cases b,
  repeat { rw to_list },
  simp,
  induction a_val generalizing b_val n,
  case list.nil {
    cases b_val,
    { refl },
    {
      rw list.length at a_property b_property,
      rw ← b_property at a_property,
      contradiction,
    }
  },
  case list.cons {
    cases b_val,
    {
      rw list.length at a_property b_property,
      rw ← b_property at a_property,
      contradiction,
    },
    {
      have : _ := hieq ⟨0, sorry⟩,
      rw [vector.nth, list.nth_le, vector.nth, list.nth_le] at this,
      dunfold vector.nth at hieq,
      rw this,
      simp,
      cases a_property,
      apply a_val_ih,
      repeat { sorry },
    }
  }
end
-- | ⟨[], _⟩ ⟨[], ha⟩ _ _ := by refl
-- | ⟨ a :: as , _⟩ ⟨ b :: bs, _⟩ i hieq := begin
  
-- end


--   intros i hieq,
--   exact match a with
--   | ⟨[], ha⟩ := 
--     begin
--       exact match b with
--       | ⟨[], ha⟩ := sorry
--       |
--       end,
--     end
--   end
-- end

@[simp] lemma vector_0_eq {α : Type} : ∀(v : vector α 0), v = vector.nil
| ⟨l, hl⟩ := subtype.eq $ show l = list.nil, from list.length_eq_zero.1 hl

lemma vector_0_eq' {α : Type} {v v' : vector α 0} : v = v' := sorry

@[simp] lemma map₂_nil {α β γ : Type} {f : α → β → γ} :
  ∀ (v : vector α 0) w, vector.map₂ f v w = vector.nil
| ⟨[], _⟩ ⟨[], _⟩ := by simp [vector.map₂, vector.nil]

@[simp] lemma map₂_nil' {α β γ : Type} {f : α → β → γ} (v : vector α 0) (p) :
  vector.map₂ f v ⟨list.nil, p⟩ = vector.nil := sorry

@[simp] lemma nth_map (f : α -> β) (v : vector α n) (i) : (v.map f).nth i = f (v.nth i) := match v with
| ⟨l, hl⟩ := begin unfold nth map, sorry end
end

@[simp] lemma nth_map₂ (f : α → β → γ) (v : vector α n) (w : vector β n) (i) : nth (map₂ f v w) i = f (v.nth i) (w.nth i) := sorry

lemma map_map (g : β → γ) (f : α → β) (v : vector α n) : map g (map f v) = map (g ∘ f) v := begin
  cases v,
  apply vector.eq,
  simp [to_list, map, list.map_map],
end

lemma map₂_map₂ (g : γ → β → δ) (f : α → β → γ) (v : vector α n) (v' : vector β n) : map₂ g (map₂ f v v') v' = map₂ (λ a b, g (f a b) b) v v' := begin
  cases v,
  cases v',
  apply vector.eq,
  simp [to_list, map, map₂],
  apply list.map₂_map₂,
end

-- example {f a as b bs h h' h''} :
--   vector.map₂ f ⟨ a :: as, h⟩ ⟨b :: bs, h'⟩ = ⟨f a b :: vector.map₂ f as bs, h''⟩ :=
-- sorry

def range (n : ℕ) : vector ℕ n := ⟨list.range n, sorry⟩

lemma range_nth {n : ℕ} {i : fin n} : (range n).nth i = i := sorry

def range_fin (n : ℕ) : vector (fin n) n := ⟨list.range_fin n, sorry⟩

@[simp] lemma length_map {α n} (f : α → β) (l : vector α n) : length (map f l) = length l := sorry

@[simp] lemma length_range_nth : length (range_fin n) = n := sorry

lemma eq_one {α : Type} (v : vector α 1) (v' : vector α 1) : v.nth ⟨0, sorry⟩ = v'.nth ⟨0, by sorry⟩ ↔ (v = v') := sorry

lemma eq_one' {α : Type} (a b : α) : a = b ↔ (v[a] = v[b]) := sorry

lemma length_list {α : Type} {n} {v : vector α n} : list.length (vector.to_list (v)) = vector.length v := begin
  admit,
end

lemma map_single {α β : Type} (f : α → β) (e : α) : vector.map f v[e] = v[f e] := begin
    refl,
end

end vector

namespace bool

lemma eq_tt_coe {b : bool} : b ↔ (b = tt) := begin
  sorry,
end

lemma bnot_bnot {α : Type} {f : α → bool} : (bnot ∘ bnot ∘ f) = f := begin
  sorry,
end

lemma bnot_ff (b : bool) : bnot b = (b = ff) := begin
  by_cases b = ff,
  { rw h, refl, },
  { simp at h, subst h, simp, }
end

end bool