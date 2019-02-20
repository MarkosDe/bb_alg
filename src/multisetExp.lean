import data.polynomial linear_algebra.multivariate_polynomial
import ring_theory.ideals data.nat.choose order.zorn
import algebra.module
open set
open ring
open polynomial


universes u
variables {α : Type u}{σ : Type*} [decidable_linear_order σ]

variables {ms1 ms2: multiset σ}(f : σ)
#check multiset.insert_eq_cons f ms1
#check multiset.join {ms1, ms2}

variables {a b c : α}{ms: multiset α}

#eval multiset.count 3 {3, 3, 3, 2, 1, 44, 322, 2}
#eval multiset.count 8 {3, 3, 3, 2, 1, 44, 322, 2}

#eval @multiset.join ℕ {{2, 3}, {1, 4}}

#eval multiset.join ({({3, 2} : multiset ℕ), ({5, 8} : multiset ℕ)} : multiset (multiset ℕ))
#check @multiset.join
-- instance le_on_finsupp: has_le (σ →₀ ℕ) :=
--      ⟨ λM N, ∃ (X Y : σ →₀ ℕ), (∀s, N s = (M s - X s) + Y s) ∧ (∀ y ∈ Y, ∃x ∈ X, x ≥ y) ⟩  

--take ns and add n copies of a
#check multiset.repeat
#eval multiset.repeat ({2, 3} : multiset ℕ) 5
#eval multiset.repeat 3 6


--add σ to multiset
def multiset.add_repeats_nat (ns: multiset ℕ) (a: ℕ) (n: nat):= (multiset.repeat a n) + ns
#check @multiset.add_repeats_nat
#eval multiset.add_repeats_nat ({2, 3} : multiset ℕ) 3 2
#eval multiset.add_repeats_nat ({}:multiset ℕ) 3 2

--count multiplicity of element
#eval multiset.count 3 {3,2,1,3}
--extract max number 
#eval max (multiset.count 3 {3,2,1,3})(multiset.count 1 {3,2,1,3})

def f3: finsupp ℕ ℚ :=
  finsupp.single 1.3 103 +
  finsupp.single 7 200

def f5 : finsupp (multiset ℕ) ℚ :=
finsupp.single {3, 2} 100 + 
finsupp.single {4, 4, 5} 20
#eval f3 1.3
#eval f5 {3,2}

#check (f5 : my_mvpolynomial ℕ ℚ)
#check my_mvpolynomial.l_t _ _ f5

#eval list.find (λ c : nat, c > 4) [1,2,5,8]
#eval (λ x, x + 2) 7

--is ok
def witness (l2 : list (list ℕ)) : option (list ℕ) :=
   list.find (λ x : list ℕ, x.head > 3) l2
#eval witness [[1,2,3],[2,5,6],[9,1,4],[10]]  
#check λ x : list ℕ, x.head > 3

--from mathlib
/-- `lookmap` is a combination of `lookup` and `filter_map`.
  `lookmap f l` will apply `f : α → option α` to each element of the list,
  replacing `a -> b` at the first value `a` in the list such that `f a = some b`. -/
def lookmap (f : α → option α) : list α → list α
| []     := []
| (a::l) :=
  match f a with
  | some b := b :: l
  | none   := a :: lookmap l
  end