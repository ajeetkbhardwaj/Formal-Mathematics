/-
Problem-0 :
If x, q are natural numbers then show that 37 * x + q = 37 * x + q

Given : x, q : Nat
Goal  : Prove equality of both side expressions.
Tool  : rfl (reflexivity)
-/

theorem problem0 (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl

-- Alternatively as an example
example (x q : Nat) : 37 * x + q = 37 * x + q := by rfl

 
/-
Problem-1 :
If x and y are natural numbers, and y = x + 7,
then prove that 2 * y = 2 * (x + 7).

Given : x, y : Nat, and hypothesis h : y = x + 7
Goal  : 2 * y = 2 * (x + 7)
Tools : rw [h], rfl
-/

theorem problem1 (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]   -- Replace y with x + 7 using the hypothesis
  rfl      -- Reflexivity: both sides are now identical

-- Alternatively as an example
example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]
  rfl
 
 
/-
Problem-2 :
Prove that 2 is the number after the number after zero.

Mathematical meaning:
2 = Nat.succ (Nat.succ 0)
-/

theorem problem2 : 2 = Nat.succ (Nat.succ 0) := by
  rw [Nat.succ_one_eq_two]      -- replace 2 with succ 1
  rw [Nat.succ_zero_eq_one]     -- replace 1 with succ 0
  rfl

-- Alternatively, reverse direction using ← to rewrite from right to left
theorem problem2_alt : Nat.succ (Nat.succ 0) = 2 := by
  rw [← Nat.succ_one_eq_two]     -- replace succ 1 with 2
  rw [← Nat.succ_zero_eq_one]    -- replace succ 0 with 1
  rfl
