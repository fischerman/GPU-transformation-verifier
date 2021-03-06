import data.set.basic

namespace MCL


inductive type
| int
| float

open type

@[reducible]
def signature := string → type

@[reducible]
def create_signature : list (string × type) → signature
| [] n := int
| ((m, t) :: xs) n := if m = n then t else create_signature xs n

@[reducible]
def type_map : type → Type
| int := ℕ
| float := ℕ

@[reducible]
def state (sig : signature) : Type := Π n : string, type_map (sig n)

def state.update {sig : signature} (name : string) (val : type_map (sig name)) (s : state sig) : state sig :=
λn, if h : n = name then by rw [h]; exact val else (s n)

def state.update' {sig : signature} {t : type} {name : string} (eq : sig name = t) (val : type_map t) (s : state sig) : state sig :=
state.update name (by rw [eq]; exact val) s

def state.get' {sig : signature} {t : type} {name : string} (eq : sig name = t) (s : state sig) : type_map t :=
by rw [← eq]; exact s name

inductive expression (sig : signature) (t : type) : Type
| var (n : string) (h : sig n = t) : expression
| add : expression → expression → expression
| const_int {} (n : ℕ) (h : t = int) : expression

instance (sig : signature) (t : type) : has_add (expression sig t) := ⟨expression.add⟩
instance (sig : signature) : has_zero (expression sig int) := ⟨expression.const_int 0 rfl⟩
instance (sig : signature) : has_one (expression sig int) := ⟨expression.const_int 1 rfl⟩

notation `v(` n `)`:= expression.var n (by refl)
infixr ` ~+ `:90 := expression.add
notation `i(` n `)`:= expression.const_int n (by refl)

open expression

inductive program (sig : signature)
| assign (n : string) : list (expression sig int) → (expression sig (sig n)) → program
| seq : program → program → program
| loop (n : string) (h : sig n = int) :
  expression sig int → program → program
| skip : program

infixr ` ;; `:90 := program.seq

open program

def type_map_add : Π{t : type}, type_map t → type_map t → type_map t
| int a b := a + b
| float a b := a + b

def eval_expression {sig : signature} (s : state sig) {t : type} : expression sig t → type_map t
| (var n h) := (by rw [←h]; exact s n)
| (add a b) := type_map_add (eval_expression a) (eval_expression b)
| (const_int n h) := (by rw [h]; exact n)

def den {sig : signature} : program sig → state sig → state sig
| (assign var_name indices expr) s := s.update var_name (eval_expression s expr)
| (seq p₁ p₂) s := den p₂ (den p₁ s)
| (loop loop_var h expr p) s' := nat.iterate (λ s, (den p s).update' h (s.get' h + 1)) (eval_expression s' expr) (s'.update' h 0)
| (skip _) s := s

notation `⟦` p `⟧`:= den p

inductive big_step {sig : signature} : (program sig × (state sig)) → (state sig) → Prop
| skip {s} :
    big_step (skip sig, s) s
| seq {p₁ p₂ s t u} (h₁ : big_step (p₁, s) t) (h₂ : big_step (p₂, t) u) : 
    big_step (seq p₁ p₂, s) u
| assign {var_name indices s u ty} {expr : expression sig ty} (hvty : sig var_name = ty) 
    (h : state.get' hvty u = eval_expression s expr) (h₂ : ∀m, ¬(var_name = m) → s m = u m) :
    big_step (assign var_name indices expr, s) u
| loop_zero {n hni expr p s} (h : eval_expression s expr = 0) : 
    big_step (loop n hni expr p, s) s
| loop_step {l hli expr p s u v} {n : type_map int} (h₁ : eval_expression s expr = (n + 1)) (h₂ : big_step (loop l hli i(n) p, u) v) (h₃ : big_step (p, s) v) :
    big_step (loop l hli expr p, s) v

infix ` ⟹ `:110 := big_step

@[reducible]
def S1 := (create_signature [("m", int), ("n", int)])

def s : state S1 := sorry

#eval eval_expression s i(10)

def P1 : program S1 :=
    (assign "n" [] i(3)) ;;
    (assign "m" [] (i(39) + v("n")))

#reduce den P1 s "m" -- computes 42
example (s : state S1) : (show nat, from den P1 s "m") = 42 := rfl

example {α β : Sort} (h : α = β) (b : β) : eq.mpr h b = eq.mpr h b := begin
    refl,
end

example {α β : Sort} (h₁ : β = α) (h₂ : α = β) (b : β) : eq.mpr h₁ (eq.mpr h₂ b) = b := begin
    refl,
end

theorem eq_mpr_switch {α β : Sort} {a b} (h : α = β)  : a = eq.mpr h b → eq.mpr (eq.symm h) a = b := begin
    intro, 
    refl,
end

theorem eq_mpr_switch' {α β : Type} {a : α} {b : β} (h : α = β)  : eq.mpr (eq.symm h) a = b → a = eq.mpr h b := begin
    intro,
    sorry
end

-- set_option pp.all true

theorem w {n v} {sig : signature} {s u : state sig} (ht : sig v = int) (hp : (assign v list.nil (const_int n ht), s) ⟹ u) : u.get' ht = n := begin
    cases hp,
    rw state.get' at hp_h,
    apply eq_mpr_switch',
    rw hp_h,
end

example {t} : (P1, s)⟹t → (t "m") = (42 : nat) := begin
    intro p,
    cases p with _ _ _ _ u _ p₁ p₂,
    have a : (show nat, from u "n") = 3 := begin
        cases p₁,
        rw eq.mpr  at p₁_h,
        rw state.get' at p₁_h,
        
    end,
    cases p_h₂,
    simp at p_h₂_hvty,
    unfold S1 at p_h₂_hvty,

end

def P2 : program S1 :=
    (assign "m" [] i(0)) ;;
    (loop "n" (by refl) i(4)) (
        (assign "m" [] (v("m") ~+ v("n"))
    ))

#eval den P2 s "m"

set_option trace.simplify.rewrite true

example (sig : signature) (p₁ p₂ : program sig) (s : state sig) : ⟦ p₁ ;; p₂ ⟧ s = den p₂ (den p₁ s) := by reflexivity

--set_option pp.all true

lemma eval_const_int { sig : signature } { s : state sig } (n : ℕ) : @eval_expression sig s int (const_int n (by refl)) = n := by refl

-- overapproximated
def modifies {sig : signature} : program sig → set (string)
| (assign n _ _) := { n }
| (seq p₁ p₂) := modifies p₁ ∪ modifies p₂
| (loop n _ _ p) := { n } ∪ modifies p

def expr_reads {sig : signature} {t : type} : expression sig t → set (string)
| (var n _) := { n }
| (add s₁ s₂) := expr_reads s₁ ∪ expr_reads s₂
| (const_int  _ _) := { }

#check (@var S1 int "m" (by refl))

#reduce expr_reads (@const_int S1 int 39 (by refl)) -- empty set
-- sets aren't computable
--#reduce expr_reads (@var S1 int "m" (by refl)) "m"

example : "m" ∈ expr_reads (@var S1 int "m" (by refl)) :=
begin
    rw expr_reads,
    simp,
end

-- does not include array accesses yet
def reads { sig : signature } : program sig → set (string)
| (assign _ _ expr) := expr_reads expr
| (seq p₁ p₂) := reads p₁ ∪ reads p₂
| (loop _ _ expr p) := expr_reads expr ∪ reads p

def uses {sig : signature} : program sig → set (string)
| p := modifies p ∪ reads p


@[simp]
lemma state_update_lookup_success (sig : signature) (s : state sig) (a : string) (va : type_map (sig a))
    : (s.update a va) a = va :=
begin
    unfold state.update,
    simp,
    rw eq.mpr,
end

@[simp]
lemma state_update_lookup_skip (sig : signature) (s : state sig) (a b : string) (va : type_map (sig a))
    : ¬(b = a) → (s.update a va) b = s b :=
begin
    intro hneq,
    unfold state.update,
    simp[hneq],
end

@[simp]
lemma state_update_lookup_skip' (sig : signature) (s : state sig) (a b : string) (va : type_map (sig a))
    : ¬(a = b) → (s.update a va) b = s b :=
begin
    intro hneq,
    apply state_update_lookup_skip,
    intro,
    apply hneq,
    simp[*]
end

lemma state_update_assoc (sig : signature) (s : state sig) (a b: string) (va : type_map (sig a)) (vb : type_map (sig b))
    : ¬(a = b) → state.update a va (state.update b vb s) = state.update b vb (state.update a va s) :=
begin
    intro hneq,
    funext x,
    -- we do case distinction, either x is a or b or neither
    by_cases hxa : x = a,
    {
        rw hxa,
        simp,
        rw state_update_lookup_skip,
        simp,
        assumption
    }, {
        by_cases hxb : x = b,
        {
            rw hxb,
            simp,
            rw state_update_lookup_skip',
            simp,
            assumption
        }, {
            repeat { rw state_update_lookup_skip },
            repeat { assumption }
        }
    }
end

lemma state_eliminate_update' (sig : signature) (s : state sig) (a b : string) (t : type) (hat : sig a = t) (hnab : ¬(b = a) ) (val : type_map t)
  : (s.update' hat val) b = s b :=
begin
    rw state.update',
    apply state_update_lookup_skip,
    assumption,
end

lemma uses_neq (sig : signature) (p : program sig) (a b : string) (hpua : uses p a) (hpnub : ¬(uses p b)) : ¬(a = b) := begin
    cases hpua,
    case or.inl {
        intro heq,
        apply hpnub,
        rw uses,
        left,
        rw ← heq,
        exact hpua
    },
    case or.inr {
        intro heq,
        apply hpnub,
        rw uses,
        right,
        rw ← heq,
        exact hpua
    }
end

lemma uses_loop_condition (sig : signature) (n : string)
    (h : sig n = int) (p : program sig) (expr : expression sig int)
    : uses (loop n h expr p) n := begin
    rw uses,
    left,
    rw modifies,
    left,
    simp,
end

lemma uses_not_seq_left (sig : signature) (p₁ p₂ : program sig) (a : string) : ¬uses (p₁ ;; p₂) a → ¬uses p₁ a := begin
    intro hnseq,
    intro hup1,
    apply hnseq,
    unfold uses,
    cases hup1,
    case or.inl {
        left,
        rw modifies,
        left,
        exact hup1,
    },
    case or.inr {
        right,
        rw reads,
        left,
        exact hup1
    }
end

lemma uses_not_seq_right (sig : signature) (p₁ p₂ : program sig) (a : string) : ¬uses (p₁ ;; p₂) a → ¬uses p₂ a := begin
    intro hnseq,
    intro hup2,
    apply hnseq,
    unfold uses,
    cases hup2,
    case or.inl {
        left,
        rw modifies,
        right,
        exact hup2,
    },
    case or.inr {
        right,
        rw reads,
        right,
        exact hup2
    }
end

lemma uses_not_loop_program (sig : signature) (n a : string)
    (h : sig n = int) (p : program sig) (expr : expression sig int)
    : ¬uses (loop n h expr p) a → ¬uses p a := begin
    intro hlnu,
    intro hpu,
    apply hlnu,
    rw uses,
    cases hpu,
    {
        left,
        rw modifies,
        right,
        assumption,
    }, {
        right,
        rw reads,
        right,
        assumption,
    }
end

-- potential tactic to solve uses

-- end MCL
-- namespace tactic.interactive

-- open tactic MCL

-- @[reducible]
-- meta def match_uses (n : expr) : expr → Prop
-- | `(¬uses %%p %%m) := (n = m)
-- | _ := false

-- meta instance (n : expr) : decidable_pred (match_uses n) := sorry

-- meta def solve_uses (h : name) : tactic unit := do
--   t ← target,
--   match t with
--   | `(¬uses %%p %%n) := do
--     gs <- get_goals,
--     trace "Possible candidates",
--     trace (gs.filter (match_uses n))
--   | _ := fail "Goal is not uses"
--   end

-- end tactic.interactive

-- namespace MCL

-- open expression program

#print prefix eval_expression
-- set_option pp.proofs true

lemma expr_uses_update_eliminate (sig : signature) (s : state sig) (a : string) (val : type_map (sig a))
      (t : type) (expr : expression sig t) (hnu : ¬(expr_reads expr a))
      : eval_expression (s.update a val) expr = eval_expression s expr :=
begin
  induction expr,
  case var : n h {
    have hneq : ¬(a = n) := begin
        intro han,
        subst han,
        apply hnu,
        rw expr_reads,
        sorry -- another one of those set things
    end,
    have : state.update a val s n = s n := begin
        rw state_update_lookup_skip',
        assumption,
    end,
    simp [eval_expression, this],
  },
    case add : a b ih_a ih_b {
      simp [eval_expression],
      rw ih_a,
      rw ih_b,
      repeat { sorry } -- use the yet to written tactic
    },
    case expression.const_int : {
        simp [eval_expression],
    }
end

lemma expr_uses_update'_eliminate (sig : signature) (s : state sig) (a : string) (t t' : type)
    (hat : sig a = t) (val : type_map t) (expr : expression sig t') (hnu : ¬(expr_reads expr a))
    : eval_expression (s.update' hat val) expr = eval_expression s expr := begin
    unfold state.update',
    apply expr_uses_update_eliminate,
    exact hnu
end

lemma iterate_outer {α : Type} (f : α → α) (n : ℕ) (a : α) : f^[n+1] a = f ((f^[n]) a) := sorry

-- set_option pp.all true

lemma state_postpone_update' (sig : signature) (s : state sig) (a : string) (t : type)
    (hat : sig a = t) (val : type_map t) (p : program sig) (hnu : ¬(uses p a))
    : ⟦ p ⟧ (s.update' hat val) = (⟦ p ⟧ s).update' hat val :=
begin
    rw state.update',
    rw state.update',
    induction p generalizing s,
    case assign : b idxs expr {
        rw den,
        rw den,
        have hpub : uses (assign b idxs expr) b := begin
            rw uses,
            left,
            rw modifies,
            simp
        end,
        have hneq : ¬(b = a) := begin
            apply uses_neq sig (assign b idxs expr) b a,
            repeat { assumption }
        end,
        have hnrea : ¬expr_reads expr a := begin
            intro hrea,
            apply hnu,
            rw uses,
            right,
            exact hrea
        end,
        rw expr_uses_update_eliminate,
        repeat { exact hnrea },
        rw state_update_assoc,
        exact hneq,
    },
    case seq : p₁ p₂ ih₁ ih₂ {
        repeat { rw den },
        rw ih₁,
        {
            apply ih₂,
            apply uses_not_seq_right,
            exact hnu,
        }, {
            apply uses_not_seq_left,
            exact hnu,
        }
    },
    case loop : n h_n_is_int expr p ih {
        have hneq : ¬(n = a) := begin
            apply uses_neq _ (loop n h_n_is_int expr p),
            {
                apply uses_loop_condition,
            },
            assumption
        end,
        repeat { rw den },
        simp,
        repeat { rw state.update' },
        rw state_update_assoc,
        rw expr_uses_update_eliminate,
        generalize : (eval_expression s expr) = i,
        induction i,
        case nat.zero {
            rw nat.iterate,
            rw nat.iterate,
        },
        case nat.succ : i loop_ih {
            -- we must take of one loop, but it must the top one
            rw iterate_outer,
            rw loop_ih,
            rw ih,
            rw state.update',
            rw state_update_assoc,
            rw state.get',
            rw state_update_lookup_skip,
            --level the RHS
            rw iterate_outer,
            rw state.update',
            rw state.get',

            repeat {assumption},
            apply uses_not_loop_program,
            apply hnu,
        }, {
            --
            intro hrea,
            apply hnu,
            sorry, -- use cool new tactic
        }, {
            assumption
        }
    },
end

lemma loop_var {sig : signature} {l : string} (hli : sig l = int) (p : program sig) (n : ℕ) (s : state sig) (expr : expression sig int) (he : eval_expression s expr = n) : 
    (⟦loop l hli expr p⟧ s).get' hli = n := begin
    rw den,
    rw he,
    clear he,
    induction n,
    case nat.zero {
        rw nat.iterate,
        rw state.update',
        rw state.get',
        rw state_update_lookup_success,
        sorry
    },
    case nat.succ : n ih {
        rw iterate_outer,
        rw state.get',
        rw [ih],
        rw state.update',
        rw state_update_lookup_success,
        simp[nat.add_succ], 
        sorry,
    }
end


-- do we model for or foreach here?
lemma loop_seq (sig : signature) (l : string) (hli : sig l = int) (p : program sig) (n : ℕ) :
  ⟦ loop l hli i(n + 1) p ⟧ = ⟦ loop l hli i(n) p ;; p ;; assign l [] (const_int (n + 1) hli) ⟧ := begin
    funext s v,
    rw den,
    rw eval_const_int,
    rw iterate_outer,
    rw <- @eval_const_int sig s n,
    rw [<-den],
    rw [<-den],
    rw loop_var hli _ n _ _,
    simp,
    rw eval_const_int,
    rw [den],
    rw [den],
    rw [den],
    rw [den],
    rw [den],
    rw [den],
    rw eval_const_int,
    rw eval_const_int (1 + n),
    sorry
end


-- seq p1 p1 = loop n 2 p1
lemma loop_seq' (sig : signature) (s₁ : state sig) (v : string) (l : string) (hli : sig l = int)
        (p : program sig) (hnu : ¬(uses p l)) (hnv : ¬ (v = l)) :
        ⟦ p ;; p ⟧ s₁ v = ⟦ loop l hli i(2) p ⟧ s₁ v :=
begin
    rw den,
    rw eval_const_int,
    rw nat.iterate,
    rw nat.iterate,
    rw nat.iterate,
    rw den,
    rw state_eliminate_update' ,
    repeat { rw state_postpone_update' },
    repeat { rw state_eliminate_update' },
    repeat { assumption },
end

-- lemma : ⟦ assign a ; assign a ⟧ = ⟦ assign a ⟧

end MCL


-- todo: make sig a parameter
-- todo: introduce notation
-- todo: make signature implicit