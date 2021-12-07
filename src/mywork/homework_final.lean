/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

import tactic.ring
import algebra.algebra.basic

/-
The following problems are listed in the Problems section of 
the chapter. 
-/
--#1. Solve probem #1, first sentence only.
--Write the principle of complete induction using the notation of symbolic logic.


def P : ℕ → Prop
| (0) := true
| (n+1) := P(n)

def complete_induction : ∀ (n : ℕ), P (n) :=
begin
    -- Won't prove, just asked to state
end




/-#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs. 

    #2 Show that for every 𝑛, 0^2+1^2+2^2+…𝑛^2 = 1/6𝑛(1+𝑛)(1+2𝑛).
    Base Case 0:
     0^2 = 1/6(0)(1+0)(1+2(0))
     0 = 0

    Inductive Case: 
     Assume you are given a proof that for a natural number n, the sum of square up to n is 
     1/6n(1+n)(1+2n). Now prove that for n+1 the sum of squares is 1/6(n+1)(n+2)(2n+3))
     This can be done by taking our original case 1/6n(1+n)(1+2n) and adding (n+1)^2. 
     = 1/6(n)(1+n)(1+2n)+(n+1)^2
     = 1/6(2n^3+3n^2+n)+(n^2+2n+1)
     = 1/3n^3+1/2n^2+1/6n+n^2+2n+1
     = 1/3n^3+3/2n^2+13/6n+1
     = 1/6(n+1)(n+2)(2n+3)
     Matches the successor case

     Because the property holds true for the base case 0 of natural numbers
     and true for the successor case, the property that the sum of squares to a
     natural number n is 1/6n(1+n)(1+2n) is true by induction. 
    -/



--Final test out


--#1: Formal proof for #2

def exponent : ℕ → ℕ → ℕ 
| (m) (0) := 1 
| (m) (n+1) := m * (exponent(m)(n))

def SumSquares : ℕ → ℕ 
| (0) := 0
| (n+1) := SumSquares(n) + exponent(n+1)(2)

example : ∀ (n : ℕ), 6* SumSquares(n) = n*(1+n)*(1+2*n):=
begin
    assume n, 
    induction n with n' ih,
    unfold SumSquares,
    ring,
    rw nat.succ_eq_add_one,
    unfold SumSquares,
    rw mul_add,
    rw ih,
    unfold exponent,
    ring,
end

--#2: Formal or detailed informal proofs 10-13
--10
example : ∀ (n : ℕ), 1 * n = n :=
begin
    assume n,
    induction n with n' ih,
    exact rfl,
    rw nat.succ_eq_add_one,
    rw mul_add,
    ring,
end


--11
example : ∀ (m n k: ℕ), m*(n+k) = m*n + m*k := 
begin
    assume m n k,
    induction n with n' nih,
    rw mul_add,
    rw nat.succ_eq_add_one,
    rw mul_add,
end

--12
example : ∀ (m n k : ℕ), m*(n*k) = (m*n)*k :=
begin
    assume m n k,
    induction n with n' ih,
    ring,
    rw nat.succ_eq_add_one,
    rw mul_add,
    ring,
end

--13
example : ∀ (m n : ℕ), m * n = n * m :=
begin
    assume m n, 
    induction n with n' ih,
    ring,
    rw nat.succ_eq_add_one,
    rw mul_add,
    ring,
end 


--#3 (Extra Credit): #5 or #9
