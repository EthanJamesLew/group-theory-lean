/-
WR Scott's Group Theory in Lean
-/

namespace introduction
open nat

definition set' (A : Type) := A → Prop
notation x ∈ S := S x

-- a set is determined by its members; that is, is S and T are sets, then S = T
-- iff(*) s ∈ S iff s ∈ T
definition is_equiv {A : Type} (S T: set A) := ∀ (x : A), x ∈ S ↔ x ∈ T
infix ` = `:55 := is_equiv

-- the number of elements in a set will be called the order of S and denoted
-- by o(S)
constant order {A : Type} (S : set A) : ℕ
notation `o(`S`)` := order S

-- A set S is a singleton iff o(S) = 1, and an n-ton iff o(S) = n
constant is_singleton {A : Type} (S : set A) : Prop
constant is_nton {A : Type} (S : set A) (n : ℕ) : Prop
axiom singleton_is_o1 {A : Type} (S : set A) : is_singleton S ↔ o(S) == 1
axiom nton_is_on {A : Type} (S : set A) (n : ℕ) : is_nton S n ↔ o(S) == n

-- A set S is a subset of a set T, written S ⊂ T, iff(*) if x ∈ X → x ∈ T
definition subset {A : Type} (S : set A) (T : set A) : Prop :=
  ∀ (a : A), a ∈ S → a ∈ T
notation S ⊂ T := subset S T

-- ordered pairs (a, b) and (c, d)
class ord_pair (A B : Type) :=
  (fst : A)
  (snd : B)

-- two order pairs (a, b) and (c, d) are equal iff(*) a = c and b = d
definition ord_pair.equal {A : Type} {B : Type} (p q : ord_pair A B) : Prop :=
  p.fst == q.fst ∧ p.snd == q.snd

-- introduce this as everything uses it
variable {A : Type}

-- its inverse R⁻¹ = {(b, a) | (a, b) ∈ R}
definition inverse (R : set (ord_pair A A)) : set (ord_pair A A) :=
  {p | (⟨p.snd, p.fst⟩ : ord_pair A A) ∈ R}
postfix `⁻¹`:100 := inverse

definition symmetric (R : set (ord_pair A A)) : Prop :=
  R = R⁻¹

-- Dom(R) = {a | ∃ b with (a, b) ∈ R}
definition domain (R : set (ord_pair A A)) : set A :=
  {p.fst | ∀ (p : (ord_pair A A)), p ∈ R}
notation `Dom(`R`)` := domain R

-- Rng(R) = Dom(R⁻¹)
definition range (R : set (ord_pair A A)) : set A :=
  Dom(R⁻¹)
notation `Rng(`R`)` := range R

-- a relation is said to be from A into B iff Dom(R) = A and Rng(R) = B
definition from_into (R : set (ord_pair A A)) (S : set A) (T : set A) : Prop :=
  Dom(R) = S ∧ Rng(R) ⊂ T

-- a relation is said to be from A onto B iff B = Rng(B)
definition from_onto (R : set (ord_pair A A)) (S : set A) (T : set A) : Prop :=
  T = Rng(R)
notation R` from `S` into `T := from_into R S T
notation R` from `S` onto `T := from_onto R S T

-- if S ⊂ Dom(R), then the restriction of R to S is the set
definition restriction (R : set (ord_pair A A)) (S : set A) : set (ord_pair A A) :=
  {p | ∀ (p: ord_pair A A), p ∈ R ∧ p.fst ∈ S}
infix ` | `:55 := restriction

-- if R and R' are relations, then their product is a relation
definition product (R S : set (ord_pair A A)) : set (ord_pair A A) :=
  {p | ∃ (b : A), (⟨p.fst, b⟩ : ord_pair A A) ∈ R ∧ (⟨b, p.snd⟩: ord_pair A A) ∈ S}
infix ` * `:55 := product

-- a relation R is transitive if RR ⊂ R
definition transitive (R : set (ord_pair A A)) : Prop :=
  R * R ⊂ R

-- If R₁, R₂, and R₃ are relations, then R₁ * (R₂ * R₃) = (R₁ * R₂ * R₃)
theorem mul_assoc (R₁ R₂ R₃ : set (ord_pair A A)) : R₁ * (R₂ * R₃) = (R₁ * R₂ * R₃) :=
begin
  intro h,
  split,
  intro p,
  rw [product, product] at p,
  cases p with p₁ p₂,
  cases p₂ with p₁₁ p₁₂,
  cases p₁₂ with p₂₁ p₂₂,
  cases p₂₂ with p₃₁ p₃₂,
  rw [product, product],
  repeat {split},
  apply p₁₁,
  apply p₃₁,
  apply p₃₂,

  intro p,
  rw [product, product] at p,
  cases p with p₁ p₂,
  cases p₂ with p₁₁ p₁₂,
  cases p₁₁ with p₂₁ p₂₂,
  cases p₂₂ with p₃₁ p₃₂,
  rw [product, product],
  repeat {split},
  apply p₃₁,
  apply p₃₂,
  apply p₁₂,
end

-- the cartesian product of two sets R and S
definition cart_product (R S : set (A)) : set (ord_pair A A) :=
  {p | p.fst ∈ R ∧ p.snd ∈ S}
infix ` × `:55 := cart_product

-- a relation R is on S iff R ⊂ S × S
definition relation_on (R : set (ord_pair A A)) (S : set A) : Prop :=
  R ⊂ S × S

-- helper construction for reflexive
definition double (S : set A) : set (ord_pair A A) :=
 {p | p.fst == p.snd ∧ p.fst ∈ S}

-- A relation R on S is reflexive iff {(a, a) | a ∈ S} ⊂ R
definition reflexive (R : set (ord_pair A A)) (S : set A) : Prop :=
  double S ⊂ R

-- An equivalence relation on S is a relation on S which is reflexive, symmetric,
-- and transitive
definition equivalence (R : set (ord_pair A A)) (S : set A) : Prop :=
  reflexive R S ∧ symmetric R ∧ transitive R

-- create an equivalence relation construction
class EquivalenceRelation (A : Type) :=
  (equiv : set (ord_pair A A)) (S : set A)
  (reflexive : reflexive equiv S)
  (symmetric : symmetric equiv)
  (transitive : transitive equiv)

definition is_equiv_on (R : set (ord_pair A A)) (S : set A) : Prop :=
  reflexive R S ∧
  symmetric R ∧
  transitive R

-- If R is an equivalence relation on S, the a subset B of S is an equivalence class
-- with respect ro R ↔ ∃ a ∈ S such that B = {b | (a, b) ∈ R}
definition equivalence_class [R : EquivalenceRelation A] (S B : set A) := 
  B ⊂ S ↔ (∃ (a : A), a ∈ S ∧ {b | (⟨a, b⟩ : ord_pair A A) ∈ R.equiv} = B)

-- less general union defined earlier (for exercises)
definition union (S T : set A) : set A :=
  {a | a ∈ S ∨ a ∈ T}
infix ` ∪ `:100 := union

-- less general intersection defined earlier (for exercises)
definition intersection (S T : set A) : set A :=
  {a | a ∈ S ∧ a ∈ T}
infix ` ∩ `:100 := intersection

definition is_function (R : set (ord_pair A A)) : Prop :=
  ∃ (a b c: A), ((⟨a, b⟩ : ord_pair A A) ∈ R ∧ (⟨a, c⟩ : ord_pair A A) ∈ R) → (b == c)

class Function (A : Type) :=
  (relation : set (ord_pair A A))
  (func_cond : is_function relation) 

-- can't I just overload the notation?
notation `fDom(`R`)` := domain R.relation
notation `fRng(`R`)` := range R.relation

definition Function.apply (R : Function A) (a : A) : A := sorry
  
definition Function.equiv (A : Type) [f : Function A] [g : Function A] : Prop :=
  fDom(f) = fDom(g) ∧ ∀ a, a ∈ fDom(f) ∧ f.apply a == g.apply a

definition invertible (f : Function A) : Prop := 
  is_function(f.relation⁻¹)

lemma simple_fun (f : Function A) : is_function (f.relation) :=
begin
  rw is_function,
  apply f.func_cond,
end

-- this is incomplete
theorem prod_function (f g : Function A) : is_function (f.relation * g.relation) :=
begin
  -- i get weird stuff later on
  --let (a, d) and (a, e) ∈ fg. Then ∃ b st (a, b) ∈ f and (b, d) ∈ g
  -- and ∃ c st (a, c) ∈ f and (c, e) ∈ g. Since f and g are functions, 
  -- then b = c and d = e. so fg is a function.
  sorry,
end

-- I don't know how to get lean to do this for me
lemma simp_or_member {A : Type} (S T : set A) (q : A): q ∈ {x | x ∈ S ∨ x ∈ T} ↔ q ∈ S ∨ q ∈ T :=
begin
  split,
  repeat {
    intro h,
    apply h
  },
end

lemma simp_and_member {A : Type} (S T : set A) (q : A): q ∈ {x | x ∈ S ∧ x ∈ T} ↔ q ∈ S ∧ q ∈ T :=
begin
  split,
  repeat {
    intro h,
    apply h
  },
end

section exercise
-- Exercise 1.1.4
-- show that ∪ and ∩ are commutative and associative (as binary operations) 
example : ∀ (S T : set A), S ∪ T = T ∪ S :=
begin
  intros s t,
  repeat {rw union},
  intro p,
  simp [or.comm],
end

-- intersection is commutative
example : ∀ (S T : set A), S ∩ T = T ∩ S :=
begin
  intros s t,
  repeat {rw intersection},
  intro p,
  simp [and.comm],
end

-- union is associative
example : ∀ (S T U: set A), S ∪ T ∪ U = S ∪ (T ∪ U) :=
begin
  intros s t u,
  intro q,
  split,
  intro p,
  repeat {rw union at p},
  repeat {rw union},
  simp [simp_or_member],
  simp [simp_or_member] at p,
  simp [or.assoc] at p,
  apply p,

  intro p,
  repeat {rw union at p},
  repeat {rw union},
  simp [simp_or_member],
  simp [simp_or_member] at p,
  simp [or.assoc],
  apply p,
end

-- intersection is associative
example : ∀ (S T U: set A), S ∩ T ∩ U = S ∩ (T ∩ U) :=
begin
  intros s t u,
  intro q,
  split,
  intro p,
  repeat {rw intersection at p},
  repeat {rw intersection},
  simp [simp_and_member],
  simp [simp_and_member] at p,
  simp [and.assoc] at p,
  apply p,

  intro p,
  repeat {rw intersection at p},
  repeat {rw intersection},
  simp [simp_and_member],
  simp [simp_and_member] at p,
  simp [and.assoc],
  apply p,
end

-- Exercise 1.1.5
-- If A and B are sets, then A = B ↔ A ⊂ B ∧ B ⊂ A
-- we don't actually know symmetry, but we can prove it
lemma equiv_symm {A : Type} (S T: set A) : S = T ↔ T = S :=
begin
  split,
  repeat {
    intros h,
    rw is_equiv,
    rw is_equiv at h,
    intro x,
    rw h,
  },
end

example (A' B' : set A): A' = B' ↔ A' ⊂ B' ∧ B' ⊂ A' :=
begin
  split,

  intros p,
  split,
  rw subset,
  intros q r,
  rw ← equiv_symm at p,
  rw p,
  apply r,

  rw subset,
  intros q r,
  rw p,
  apply r,

  intros p,
  rw is_equiv,
  intros q,
  split,

  cases p with pl pr,
  rw subset at pl,
  rw subset at pr,
  intros r,
  apply pl,
  apply r,

  cases p with pl pr,
  rw subset at pl,
  rw subset at pr,
  intros r,
  apply pr,
  apply r,
end  
end exercise

-- Exercise 1.1.6
-- TODO

-- Exercise 1.1.7
example (R : set (ord_pair A A)) (S : set A) : 
  symmetric R ∧ transitive R → is_equiv_on (R ∪ {p | p.fst == p.snd ∧ p.fst ∈ S}) S :=
begin
  intro h,
  rw is_equiv_on,
  split,
  sorry,
  sorry,
end

-- Exercise 1.1.14
example (R₁ R₂ : set (ord_pair A A)) : (R₁ * R₂)⁻¹ = ((R₂⁻¹) * (R₁⁻¹)) :=
begin
  intros h,
  split,
  intros q,
  rw [product] at q,
  cases q with p q,
  cases q with q r,
  rw [product, inverse, inverse],
  repeat {split},
  apply r,
  apply q,

  intros q,
  rw [product, inverse, inverse] at q,
  cases q with p q,
  cases q with q r,
  rw [product],
  repeat {split},
  apply r,
  apply q,
end

end introduction