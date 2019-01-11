
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

notation `v(` n `)`:= expression.var n (by refl)
infixr ` ~+ `:120 := expression.add
notation `i(` n `)`:= expression.const_int n (by refl)

open expression

inductive program (sig : signature)
| assign (n : string) : list (expression sig int) → (expression sig (sig n)) → program
| seq : program → program → program
| loop (n : string) (h : sig n = int) :
  expression sig int → program → program

notation n `::=` expr:100 := program.assign n [] expr
infixr ` ;; `:90 := program.seq
notation `for` `(` n `::=` expr `)` `{` p `}`:110 := program.loop n (by refl) expr p

open program


def eval_expression {sig : signature} (s : state sig) : Π{t : type}, expression sig t → type_map t
| t (var n h) := (by rw [←h]; exact s n)
| int (add a b) := eval_expression a + eval_expression b
| float (add a b) := eval_expression a + eval_expression b
| t (const_int n h) := (by rw [h]; exact n)  -- why does this one accept a signature but var does not

def den {sig : signature} : program sig → state sig → state sig
| (assign var_name indices expr) s := s.update var_name (eval_expression s expr)
| (seq p₁ p₂) s := den p₂ (den p₁ s)
| (loop loop_var h expr p) s' := nat.iterate (λ s, (den p s).update' h (s.get' h + 1)) (eval_expression s' expr) (s'.update' h 0)

notation `⟦` p `⟧`:= den p


@[reducible]
def S1 := (create_signature [("m", int), ("n", int)])

def s : state S1 := sorry

#eval eval_expression s i(10)

def P1 : program S1 :=
    "n" ::= i(3) ;;
    (assign "m" [] (i(39) ~+ v("n")))

#reduce den P1 s "m" -- computes 42
example (s : state S1) : (show nat, from den P1 s "m") = 42 := rfl

def P2 : program S1 :=
    "m" ::= i(0) ;;
    for ("n" ::= i(4)) {
        assign "m" [] (v("m") ~+ v("n"))
    } 

#eval den P2 s "m"

set_option trace.simplify.rewrite true 

example (sig : signature) (p₁ p₂ : program sig) (s : state sig) : ⟦ p₁ ;; p₂ ⟧ s = den p₂ (den p₁ s) := by reflexivity

lemma eval_const_int { sig : signature } { s : state sig } (n : ℕ) : @eval_expression sig s int (const_int n (by refl)) = n := begin
    rw eval_expression,
    rw eq.mpr,
end

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
    sorry
end

-- does not include array accesses yet
def reads { sig : signature } : program sig → set (string)
| (assign _ _ expr) := expr_reads expr
| (seq p₁ p₂) := reads p₁ ∪ reads p₂
| (loop _ _ expr p) := expr_reads expr ∪ reads p

def uses {sig : signature} : program sig → set (string) 
| p := modifies p ∪ reads p

-- (a != b) : get a (update b s) = get a s
-- (a != b) : (update a s) b = s b

lemma state_eliminate_update' (sig : signature) (s : state sig) (a b : string) (t : type) (hat : sig a = t) (hnab : ¬(b = a) ) (val : type_map t) 
  : (s.update' hat val) b = s b :=
begin
    rw state.update',
    rw state.update,
    show dite (b = a) (λ (h : b = a), eq.mpr _ (eq.mpr _ val)) (λ (h : ¬b = a), s b) = s b, 
    rw dite,
    cases string.has_decidable_eq b a,
    {
        refl
    }, {
        contradiction
    }
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

lemma expr_uses_update'_eliminate (sig : signature) (s : state sig) (a : string) (t : type) 
    (hat : sig a = t) (val : type_map t) (expr : expression sig t) (hnu : ¬(expr_reads expr a))
    : eval_expression (s.update' hat val) expr = eval_expression s expr := begin
    induction expr,
    case var {
        -- how do I unfold eval_expression
        sorry
    },
    sorry,
    sorry
end

lemma state_postpone_update' (sig : signature) (s : state sig) (a : string) (t : type) 
    (hat : sig a = t) (val : type_map t) (p : program sig) (hnu : ¬(uses p a)) 
    : ⟦ p ⟧ (s.update' hat val) = (⟦ p ⟧ s).update' hat val :=
begin
    induction p,
    case assign : b idxs expr {
        rw den,
        rw den,
        have hpub : uses (assign b idxs expr) b := begin
            rw uses,
            left,
            rw modifies,
            sorry -- how???
        end,
        have hneq : ¬(b = a) := begin
            apply uses_neq sig (assign b idxs expr) b a,
            repeat { assumption }
        end,
        rw ← expr_uses_update'_eliminate,
    }
end

-- seq p1 p1 = loop n 2 p1
lemma loop_seq (sig : signature) (s₁ : state sig) (v : string) (l : string) (hli : sig l = int) 
        (p : program sig) (hnu : ¬(uses p l)) (hnv : ¬ (v = l)) : ⟦ p ;; p ⟧ s₁ v = ⟦ loop l hli i(2) p ⟧ s₁ v :=
begin
    rw den,
    rw eval_const_int,
    rw nat.iterate,
    rw nat.iterate,
    rw nat.iterate,
    rw den,
    rw state_eliminate_update',
    repeat { rw state_postpone_update' },
    repeat { rw state_eliminate_update' },
    repeat { assumption },
end

end


-- todo: make sig a parameter
-- todo: introduce notation
-- todo: make signature implicit