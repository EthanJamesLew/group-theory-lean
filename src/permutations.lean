/-
WR Scott's Group Theory in Lean

Permutation Groups
-/
import .definitions

namespace permutations
variables {A M U : Type}

 definition injective (f : A → A) : Prop :=
    ∀ x y, f x = f y → x = y

-- a permutation of a set M is a 1-1 function into M onto M
-- Sym(M) is a set of permutation of M, (f : M → M) ∈ Sym(M)
-- Sym is a group, fg is the binary operation (function product)
class Sym (A : Type) :=
  (perms : set (A → A))
  (mult : (A → A) → (A → A) → (A → A))
  (symm : ∀ (f : (A → A)), (f ∈ perms) → injective f)
infix ∘ := Sym.mult

-- to prove subgroup, start with a set S
-- show that multiplication membership holds
-- show that one membership holds
-- show that inverse membership holds
class subgroup [definitions.Group (U → U)] (S : set (U → U)) : Prop :=
  (mul_mem : ∀ {a b}, a ∈ S → b ∈ S → a * b ∈ S)
  (one_mem : definitions.Group.one ∈ S)
  (inv_mem: ∀ {a}, a ∈ S → (definitions.Group.inv a) ∈ S)

-- Exercise 1.3.1 if M is a set and Sym M is a set of permutations of M,
-- the Sym M is a group 
theorem is_group [definitions.Group (A → A)] [S : Sym A] : subgroup (S.perms) := 
begin
  refine {..},
  intros p p q r,
  -- proof that f * g ∈ S
  -- f ∘ g is a function by theorem
  -- prove that f * g is onto S
  -- prove that f * g is one - to - one
  -- then f ∘ g is a permutation of M  
  repeat {sorry},
end
end permutations