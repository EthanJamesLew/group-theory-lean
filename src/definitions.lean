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
  (mul : A → A → A)
  (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
  (inv : A → A)
  (one : A)
  (mul_one : ∀ a, mul a one = a) 
  (mul_inv : ∀ a, mul a (inv a) = one)
  -- I should prove this...
  (inv_inv : ∀ a, inv (inv a) = a)

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
          ... = ((a⁻¹) * one) * (a⁻¹)⁻¹ : by simp [Group.inv_inv]
          ... = a⁻¹ * (a⁻¹)⁻¹: by rw Group.mul_one
          ... = one : by rw ←Group.mul_inv

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

-- Exercise 1.2.3
example [G : Group A] (a b : A) : ∃ x, (a * x = b) :=
begin 
  split,
  rw prod_to_inv,
end

end definitions