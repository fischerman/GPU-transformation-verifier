
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

@[reducible]
def update {sig : signature} (name : string) (val : type_map (sig name)) (s : state sig) : state sig := 
    λ n, 
    -- if n = name then val else (s n)
    begin
        by_cases n = name,
        {
            rw h,
            exact val
        }, {
            apply s,
        }
    end 

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

open program

def eval_expression {sig : signature} (s : state sig) : Π{t : type}, expression sig t → type_map t
| _ (var sig n) := s n
| _ (add int a b) := eval_expression a + eval_expression b
| _ (add float a b) := eval_expression a + eval_expression b
| _ (const_int sig a) := a

def den {sig : signature} : program sig → state sig → state sig
| (assign var_name indices expr) s := update var_name (eval_expression s expr) s
| (seq p₁ p₂) s := den p₂ (den p₁ s)
| (loop loop_var h expr p) s := nat.iterate (λ s, update loop_var (s loop_var + 1) (den p s)) (eval_expression s expr) (update loop_var 0 s)


def S1 := (create_signature [("m", int)])

def s : state S1 := sorry

def P1 : program S1 :=
assign "m" [] (add int (const_int S1 39) (const_int S1 3))

#reduce den P1 s "m" -- computes 42

example (s : state S1) : den P1 s "m" = 5 := sorry


end