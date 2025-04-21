import Mathlib.Tactic

-- Church numeral tutorial

-- Church numerals provide a way to encode numbers
-- in contexts where all we have is functions.

-- This is especially relevant in functional programming
-- and the lambda calculus.

-- In practice, most functional languages utilize higher-
-- performance representations of numbers

-- You can view church numerals as being similar to the
-- inductive definition of the natural numbers in lean,
-- but based on functions

-- You can view a given church numeral as a function
-- taking a function, and a value to apply it to,
-- and applying the function to it n times
def zero {α : Type} : (α → α) → α → α := fun _f g => g
def one  {α : Type} : (α → α) → α → α := fun f g => f g
def two  {α : Type} : (α → α) → α → α := fun f g => f (f g)

-- Example usage: flipping a boolean twice
#eval two (λb => !b) true

-- You can see that a given number just applies f one more time to the value g
-- therefore, the successor function (analogous to Nat.succ) should just add another f
def ChurchNat (α : Type) := (α → α) → α → α

def succ {α : Type} (n : ChurchNat α) : ChurchNat α :=
  fun f g => f (n f g)

#eval (succ two) (λb => !b) true

-- Now, our task is to see if we can prove that our definition of nat
-- is isomorphic to Nat.

-- I have provided here a skeleton of the proof.

-- For every nat, there is some church numeral.
theorem church_iso_nat {α : Type} : ∀ n : ℕ, ∃ numeral : ChurchNat α, sorry := sorry

-- But, how do we prove that they are the same?
-- We don't just want to prove that for any n, there exists any church numeral
-- Would like some ideas for this from yall
-- We could, naively, just create an "encode" function that converts
-- Nats to church numerals, then prove properties of the function.

-- For example, we could prove that for a given n, the conversion to
-- church nat invokes n calls of succ
-- Or, we could just prove that we can decode the original number

-- Lmk if you guys have any ideas on how to prove equivalence of our definition
-- of Nats and Lean's Nats

-- Skeleton of the proof
def to_church {α : Type} : ℕ → ChurchNat α  := sorry

def from_church {α : Type} : ChurchNat α → ℕ := sorry

theorem church_iso_nat' {α : Type} : ∀ n, from_church (@to_church α n) = n := sorry

-- But, is this strong enough?

-- Other ideas: proving things about the complexity of our number operations
-- e.g., succ is O(1), addition is O(?) whatever, etc.

-- Bonus project idea: we could try encoding Nat with ordinal sets
--
-- 0 := ∅
-- 1 := {∅}
-- 2 := {∅, {∅}}
-- 3 := {∅, {∅}, {∅, {∅}}}
--
-- and then, compare the two implementations
-- What kinds of crazy encodings of Nats can we come up with?
-- Church numerals aren't the limit.
-- And what kinds of numbers can we express with the varying implementations?
-- Can we express more types of numbers with Church encoding vs Set theoretic encoding?

-- Bonus bonus idea: encoding numbers inductively with lists?
-- 0 = []
-- 1 = [()]
-- 2 = [(), ()]

-- Sky's the limit.
-- End goal could be implementing stuff like Ring, Group, etc. for our types
-- Or, somehow, making a general implementation of all of these,
-- granted they are all "the same" as Nat
