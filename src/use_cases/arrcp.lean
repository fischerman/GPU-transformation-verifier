/- import rel_hoare

namespace arrcp

open parlang
open parlang.kernel

def tstate := string → ℕ

def state.update (name : string) (val : ℕ) (s : tstate) : tstate :=
λn, if n = name then val else s n

notation s ` & ` n ` ::= ` v := state.update n v s

def init := λ n : ℕ, λ name, if name = "tid" then n else 0

def arrcp₁ : program tstate (λ n : ℕ, ℕ) := program.intro (λ m : memory (λ n : ℕ, ℕ), m 0) (
    kernel.load (λ s, ⟨0, λ a, s & "n" ::= a⟩) ;;               -- load n to thread tlocal
    kernel.load (λ s, ⟨1 + s "tid", λ a, s & "temp" ::= a⟩) ;;  -- load from array a
    kernel.store (λ s, ⟨1 + s "n" + s "tid", s "temp"⟩)         -- store to array b
)

def arrcp₂ : program tstate (λ n : ℕ, ℕ) := program.intro (λ m : memory (λ n : ℕ, ℕ), 10) (
    kernel.load (λ s, ⟨0, λ a, s & "n" ::= a⟩) ;;               -- load n to thread tlocal
    kernel.compute (λ s, s & "i" ::= s "tid") ;;
    kernel.loop (λ s, s "i" < s "n") (
        kernel.load (λ s, ⟨1 + s "i", λ a, s & "temp" ::= a⟩) ;;-- load from array a
        kernel.store (λ s, ⟨1 + s "n" + s "i", s "temp"⟩) ;;    -- store to array b
        kernel.compute (λ s, s & "i" ::= s "i" + 10)
    )
)

lemma arrcprel : rel_hoare_program init init eq arrcp₁ arrcp₂ eq := begin
    unfold arrcp₁ arrcp₂,
    apply rel_kernel_to_program,
    apply single_step_left ((λ (n₁ : ℕ) (s₁ : state n₁ (string → ℕ) (λ (n : ℕ), ℕ)) (ac₁ : vector bool n₁) (n₂ : ℕ)
     (s₂ : state n₂ (string → ℕ) (λ (n : ℕ), ℕ)) (ac₂ : vector bool n₂),
       ∃ (m₁ m₂ : memory (λ (n : ℕ), ℕ)),
         state.syncable s₁ m₁ ∧
           state.syncable s₂ m₂ ∧
             n₁ = m₁ 0 ∧
               n₂ = 10 ∧
                (∀ (i : fin n₁),
                      vector.nth (s₁.threads) i =
                        {tlocal := (init ↑i) & "n" ::= m₁ 0, shared := m₁, loads := insert 0 ((vector.nth (s₁.threads) i).loads), stores := ∅}) ∧
                (∀ (i : fin n₂),
                    vector.nth (s₂.threads) i =
                        {tlocal := init ↑i, shared := m₂, loads := ∅, stores := ∅}) ∧
                    m₁ = m₂ ∧ ↥(all_threads_active ac₁) ∧ ↥(all_threads_active ac₂))),
    {
        intros n₁ n₂ s₁ s₁' s₂ ac₁ ac₂ hp hek₁,
        cases hp with m₁ hp,
        cases hp with m₂ hp,
        apply exists.intro s₂,
        apply and.intro,
        {
            suffices h : exec_state (compute id) ac₂ s₂ (state.map_active_threads ac₂ (thread_state.map id) s₂),
            {
                rw ← state.map_active_threads_id s₂ ac₂ at h,
                assumption,
            },
            apply exec_state.compute,
        }, {
            simp,
            apply exists.intro m₁,
            cases hek₁,
            apply and.intro,
            {
                
                sorry -- memory does not change
            }, {
                apply exists.intro m₂,
                apply and.intro,
                { apply hp.right.left, },
                {
                    apply and.intro hp.right.right.left (and.intro hp.right.right.right.left (and.intro _ hp.right.right.right.right.right)),
                    intro i,
                    -- rw ← hp.right.right.right.right.left,
                    simp,
                    have haa: ↥(vector.nth ac₁ i) := begin
                        apply all_threads_active_nth,
                        exact hp.right.right.right.right.right.right.right.left,
                    end,
                    simp [haa],
                    rw thread_state.load,
                    rw thread_state.load._match_1,
                    have : m₁ = (vector.nth (s₁.threads) i).shared := begin
                        rw hp.right.right.right.right.left,
                    end,
                    subst this,
                    simp,
                    have : (vector.nth (s₁.threads) i).tlocal = (init i) := begin
                        rw hp.right.right.right.right.left,
                    end,
                    rw this,
                    rw memory.get,
                    simp,
                    rw hp.right.right.right.right.left,
                }
            }
        }
    }, {

    }
end

end arrcp -/