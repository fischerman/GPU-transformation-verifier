-- non-recursive
inductive simple
| acon
| bcon

def f : simple → ℕ
| simple.acon := 1
| simple.bcon := 2

#print f
#print f._main -- uses cases on

inductive recur
| acon (r : recur)
| bcon

def g : recur → ℕ
| (recur.acon r) := g r + 1
| recur.bcon := 2

#print g
#print g._main -- uses brec_on (internally uses below)
#check @recur.cases_on
#check @recur.brec_on

inductive foo : ℕ → Type
| acon (n) (r : foo n) : foo (n + 1)
| bcon : foo 0

def h : Π {n}, foo n → ℕ
| _ (foo.acon n r) := 
    have 0 < 0 := sorry,
    h r
| n foo.bcon := 0
using_well_founded {rel_tac := λ_ _, `[exact ⟨_, measure_wf (λ ⟨n, f⟩, 0)⟩]}

#print h
#print h._main
#print h._main._pack -- I think the name pack comes from the fact that arguments 
#print id_rhs
#reduce id_rhs ℕ 2
#print h._match_1
#reduce h._match_1 ⟨0, foo.bcon⟩

inductive bar : ℕ → Type
| acon (r : bar 1) : bar 0
| bcon (n) : bar n
| ccon (n) (l : list (bar 0)) : bar n

def i : Π {n}, bar n → ℕ
| _ (bar.acon r) := i r
| _ (bar.bcon n) := 1
| _ (bar.ccon n l) := 2