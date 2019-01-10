
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

inductive expression (sig : signature) : type → Type
| var (n : string) : expression (sig n)
| add (t : type) : expression t → expression t → expression t
| const_int : ℕ → expression int

open expression

inductive program (sig : signature)
| assign (n : string) : list (expression sig int) → (expression sig (sig n)) → program
| seq : program → program → program
| loop (n : string) (h : sig n = int) :
  expression sig int → program → program

infixr ` ;; `:90 := program.seq

open program


def eval_expression {sig : signature} (s : state sig) : Π{t : type}, expression sig t → type_map t
| _ (var sig n) := s n
| _ (add int a b) := eval_expression a + eval_expression b
| _ (add float a b) := eval_expression a + eval_expression b
| _ (const_int sig a) := a

def den {sig : signature} : program sig → state sig → state sig
| (assign var_name indices expr) s := s.update var_name (eval_expression s expr)
| (seq p₁ p₂) s := den p₂ (den p₁ s)
| (loop loop_var h expr p) s' := nat.iterate (λ s, (den p s).update' h (s.get' h)) (eval_expression s' expr) (s'.update' h 0)


@[reducible]
def S1 := (create_signature [("m", int), ("n", int)])

def s : state S1 := sorry

def P1 : program S1 :=
    (assign "n" [] (const_int S1 3)) ;;
    (assign "m" [] (add int (const_int S1 39) (show expression S1 int, from var S1 "n")))

#reduce den P1 s "m" -- computes 42

example (s : state S1) : (show nat, from den P1 s "m") = 42 := rfl

-- seq p1 p1 = loop n 2 p1

end