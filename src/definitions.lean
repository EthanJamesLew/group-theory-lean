/-
WR Scott's Group Theory in Lean

Definitions and First Properties
-/
--import .preliminaries
namespace definitions
variables {A : Type}

-- A group is an ordered pair (G , ⬝), ⬝ is an associative binary operation on G
-- ∃ e ∈ G such that
-- (i) a ∈ G → a ⬝ e = a
-- (ii) a ∈ G -> ∃ a⁻¹ ∈ G, a⁻¹ ⬝ a = e 
class Group (A : Type) :=
  (one : A)
  (mul : A → A → A)
  (inv : A → A)
  (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
  (mul_one : ∀ a, mul a one = a) 
  (mul_inv : ∀ a, mul a (inv a) = one)

postfix ⁻¹ := Group.inv 
infix * := Group.mul
notation `one` := Group.one

variables [G : Group A] (a b : A)
#check a * a⁻¹ = one

-- Exercise 1.2.1
lemma inv_mul [G : Group A] (a : A): a⁻¹ * a = one :=
calc  a⁻¹ * a = a⁻¹ * a * one : by rw Group.mul_one
          ... = a⁻¹ * a * (a⁻¹ * (a⁻¹)⁻¹) : by rw Group.mul_inv
          ... = a⁻¹ * (a * a⁻¹) * (a⁻¹)⁻¹ : by simp [←Group.mul_assoc]
          ... = a⁻¹ * one * (a⁻¹)⁻¹ : by rw Group.mul_inv
          ... = ((a⁻¹) * (a⁻¹)⁻¹) : by simp [Group.mul_one]
          ... = one : by rw Group.mul_inv

-- Exercise 1.2.2
lemma one_mul [G : Group A] (a : A): one * a = a :=
calc  one * a = a * a⁻¹ * a : by rw  Group.mul_inv
          ... = a * one : by simp [Group.mul_assoc, inv_mul]
          ... = a : by simp [Group.mul_one]

-- this is essentially the proof strategy for Exercise 1.2.3
lemma prod_to_inv [G : Group A] (a b c : A): a * b = c ↔ b = a⁻¹ * c :=
begin
  split,
  intro p,
  calc b = one * b : by rw one_mul
        ... = a⁻¹ * a * b : by rw ←inv_mul
        ... = a⁻¹ * (a * b) : by rw Group.mul_assoc
        ... = a⁻¹ * c : by rw p,
  intro p,
  calc (a * b) = a * (a⁻¹ * c) : by rw ←p
        ... = (a * a⁻¹) * c : by rw Group.mul_assoc
        ... = one * c : by rw Group.mul_inv
        ... = c : by rw one_mul,
end

lemma prod_to_inv_r [G : Group A] (a b c : A): a * b = c ↔ a = c * b⁻¹ :=
begin
  split,
  intro p,
  calc a = a * one : by rw Group.mul_one
        ... = a * (b * b⁻¹) : by rw ← Group.mul_inv
        ... = (a * b) * b⁻¹: by rw Group.mul_assoc
        ... = c * b⁻¹ : by rw p,
  intro p,
  calc (a * b) = c * b⁻¹ * b : by rw ←p
        ... = c * (b⁻¹ * b) : by rw Group.mul_assoc
        ... = c * one : by rw inv_mul
        ... = c : by rw Group.mul_one,
end

-- Exercise 1.2.3
example [G : Group A] (a b : A) : ∃ x, (a * x = b) :=
begin 
  split,
  rw prod_to_inv,
end

-- Exercise 1.2.4
example [G : Group A] (a b : A) : ∃ x, (x * a = b) :=
begin 
  split,
  rw prod_to_inv_r,
end

-- Exercise 1.2.5
example [G : Group A] (a x : A) : a * x = a ↔ x = one :=
begin
  split,
  intro p,
  rw prod_to_inv at p,
  rw inv_mul at p,
  exact p,
  intro p,
  rw prod_to_inv,
  rw inv_mul,
  exact p,
end

-- Exercise 1.2.6
lemma prod_one_inv [G : Group A] (a b : A) : a * b = one ↔ b = a⁻¹ :=
begin
  split,
  intro p,
  rw prod_to_inv at p,
  rw Group.mul_one at p,
  exact p,
  intro q,
  rw q,
  rw Group.mul_inv,
end

-- Exercise 1.2.7
example [G : Group A] (a b : A) : (b⁻¹ * a⁻¹) = (a * b)⁻¹ :=
begin
  rw ←prod_one_inv,
  calc a * b * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ : by simp [Group.mul_assoc]
                      ... = a * one * a⁻¹ : by rw [Group.mul_inv] 
                      ... = a * a⁻¹ : by rw Group.mul_one
                      ... = one : by rw Group.mul_inv,
end 

-- Exercise 1.2.8
lemma inv_inv [G : Group A] (a : A) : (a⁻¹)⁻¹ = a :=
  calc  (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * one : by rw Group.mul_one
            ... = (a⁻¹)⁻¹ * (a⁻¹ * a) : by rw inv_mul
            ... = ((a⁻¹)⁻¹ * a⁻¹) * a : by simp [Group.mul_assoc]
            ... =  one * a : by rw inv_mul
            ... = a : by rw one_mul

-- Exercise 1.2.9
constant pow : ℕ → ℕ → ℕ
infix ^ := pow
axiom pow_zero (a : ℕ) : a ^ 0 = 1
axiom pow_succ (a b : ℕ) : a ^ (b.succ) = a ^ b * a
lemma one_add (a b : ℕ) : 1 + a = a.succ := by rw nat.add_comm
lemma succ_group (a b : ℕ) : (a + b).succ = a.succ + b := by admit
example (a b : ℕ) (r s : ℕ) : a^r * a^s = a^(r + s) :=
begin
  induction r with rh r,
  induction s with sh s,
  rw [nat.zero_add, pow_zero, nat.mul_one],
  rw [nat.zero_add, pow_zero, nat.one_mul],
  calc a^rh.succ * a^s = a^rh * (a * a^s) : by rw [pow_succ, nat.mul_assoc]
                  ... = a * (a^s * a^rh) : by rw [nat.mul_comm, nat.mul_assoc]
                  ... = a * (a^rh * a^s) : by simp [nat.mul_comm]
                  ... = a * a^(rh + s): by rw r
                  ... = a^(rh + s) * a: by rw nat.mul_comm
                  ... = a^((rh + s).succ) : by rw ←pow_succ
                  ... = a^(rh.succ + s) : by rw succ_group,
end
end definitions