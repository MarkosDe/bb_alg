import data.polynomial linear_algebra.multivariate_polynomial
import ring_theory.ideals data.nat.choose order.zorn
import algebra.module
open set
open ring
open polynomial
universes u
section
variables {σ : Type*} [decidable_linear_order σ]

-- '.sort' makes list
def multiset.lex (m1 m2 : multiset σ) : Prop :=
  m1.sort (≥) ≤ m2.sort (≥)

instance (m1 m2 : multiset σ) : decidable (multiset.lex m1 m2) := 
  by unfold multiset.lex; apply_instance

-- example : linear_order (list σ) := by apply_instance

lemma multiset.sort_ext {m1 m2 : multiset σ} : m1 = m2 ↔ m1.sort(≥) = m2.sort(≥) :=
iff.intro
  (sorry) 
  (assume h,
   multiset.ext.2 sorry)

def multiset.lex_is_total (σ) [decidable_linear_order σ]: decidable_linear_order (multiset σ) :=
{ le := multiset.lex,
  le_refl := λ m, le_refl _,
  le_trans := λ m1 m2 m3 h1 h2, le_trans h1 h2,
  le_antisymm := λ m1 m2 h1 h2, multiset.sort_ext.2 (le_antisymm h1 h2), 
  le_total := λ m1 m2, le_total _ _,
  decidable_le := λ _ _, by apply_instance
}
end

local attribute [instance, priority 10000] multiset.lex_is_total

-- example (σ) [decidable_linear_order σ]: 
-- ∀ a b : σ , decidable (a ≤ b) :=--decidable_rel ((≤) : multiset σ → multiset σ → Prop) :=
--  by apply_instance 

def my_mvpolynomial (σ : Type*) (α: Type*) [comm_semiring α]: Type* := 
  finsupp (multiset σ) α

variables {α : Type} {σ : Type*} [decidable_linear_order σ] [discrete_linear_ordered_field α]

--to mame * between my_mvpolynomials
instance : comm_ring (my_mvpolynomial σ α):= 
  finsupp.to_comm_ring

example : linear_order (multiset σ) := by apply_instance
example : partial_order (multiset σ) := by apply_instance

def my_mvpolynomial.coef (pol : my_mvpolynomial σ α): multiset σ -> α := 
  pol.to_fun

--DEGREE of MONOMIAL
def monomial_degree (ms: multiset σ) : ℕ :=
  multiset.card ms

def my_mvpolynomial.leading_mon (pol: my_mvpolynomial σ α ) : option (multiset σ) := 
  (finsupp.support pol).max

def degree_LM (pol: my_mvpolynomial σ α) : ℕ := 
  monomial_degree ((my_mvpolynomial.leading_mon pol).iget)

def is_zero (pol : my_mvpolynomial σ α) : bool :=
  pol = 0

def zero_ideal := ([0]: list (my_mvpolynomial σ α)) 

--variables (polt1 polt2: my_mvpolynomial σ α)

def my_mvpolynomial.leading_coef (pol: my_mvpolynomial σ α): α :=
  match (my_mvpolynomial.leading_mon pol) with
  | some ms := pol.coef ms
  | none := 0
end 

-----LEADING TERM
def my_mvpolynomial.l_t (pol: my_mvpolynomial σ α ) : my_mvpolynomial σ α :=
  finsupp.single (my_mvpolynomial.leading_mon pol).iget (my_mvpolynomial.leading_coef pol) 

--Representation of the polynomial
def my_mvpolynomial.repr [has_repr σ] [has_repr α] (p : my_mvpolynomial σ α) : string :=
  if p = 0 then "0" else ((finsupp.support p).sort multiset.lex).foldr 
  (λ ms s, let coef := p.to_fun ms in 
  s ++ (if (coef ≥ 0 ∧ s.length > 0) then " +" ++ repr coef else " " ++ repr coef) ++ repr ms ) ""

instance [has_repr σ] [has_repr α] : has_repr (my_mvpolynomial σ α) :=
  ⟨my_mvpolynomial.repr⟩

--used in for LCM of monomials 
def multiset.add_repeats (ms: multiset σ) (aa : σ) (n: nat) : multiset σ := 
  (multiset.repeat aa n) + ms

#check @multiset.add_repeats
#eval multiset.add_repeats ({} : multiset ℕ) 2 5

--finds LCM of LM1 LM2, outputs in diff order
--for every x add to {} the max repetitions from m1 m2  
def multiset.mon_LCM (m1 m2 : multiset σ) : multiset σ :=
  ((m1.to_finset) ∪ (m2.to_finset)).fold multiset.add ({}) 
  (λ x, multiset.add_repeats ({} : multiset σ) x (max (multiset.count x m1) (multiset.count x m2)))

#check multiset.mon_LCM
#eval multiset.mon_LCM ({3,3,2} : multiset ℕ) ({2,2, 8} : multiset ℕ)

def example_pol: my_mvpolynomial ℕ ℚ :=
  finsupp.single {1,3} 1 -  
  finsupp.single {2,2} 1

--representation
#eval example_pol
#eval my_mvpolynomial.leading_coef example_pol  
#eval my_mvpolynomial.leading_mon example_pol  
#eval my_mvpolynomial.l_t example_pol  

--define polyniomial examples
def f1: my_mvpolynomial ℕ ℚ :=
  finsupp.single {3,3,2} 1 -  
  finsupp.single {} 1

def f2: my_mvpolynomial ℕ ℚ :=
  finsupp.single {3,2,2} 1 -  
  finsupp.single {3} 1

def f3: my_mvpolynomial ℕ ℚ :=
  finsupp.single {3,3} 1 -  
  finsupp.single {2} 1

def f4: my_mvpolynomial ℕ ℚ :=
  finsupp.single {2,2} 1 -  
  finsupp.single {} 1

def g1: my_mvpolynomial ℕ ℚ :=
  finsupp.single {3,3} 1 +  
  finsupp.single {3,2,2} 1

def g2: my_mvpolynomial ℕ ℚ :=
  finsupp.single {3,3} 1 -  
  finsupp.single {2,2,2} 1

def g3: my_mvpolynomial ℕ ℚ :=
  finsupp.single {2,2,2} 1 -  
  finsupp.single {2,2} 1

def g4: my_mvpolynomial ℕ ℚ :=
  finsupp.single {3,2,2} 1 +  
  finsupp.single {2,2} 1

--LCM(LM1, LM2) / LM1
def s_monomial_l (pol1 pol2: my_mvpolynomial σ α): multiset σ :=
  let lmp1 := (my_mvpolynomial.leading_mon pol1).iget in 
  (multiset.mon_LCM lmp1 (my_mvpolynomial.leading_mon pol2).iget) - lmp1

#eval f1
#eval my_mvpolynomial.leading_coef f1
#eval my_mvpolynomial.leading_mon f1
#eval my_mvpolynomial.l_t f1
#eval s_monomial_l f1 f2
#eval s_monomial_l f1 f3
#eval s_monomial_l f2 f3

--LCM(LM1, LM2) / LM2
def s_monomial_r (pol1 pol2: my_mvpolynomial σ α): multiset σ :=
  let lmp2 := (my_mvpolynomial.leading_mon pol2).iget in 
  (multiset.mon_LCM (my_mvpolynomial.leading_mon pol1).iget lmp2) - lmp2

#eval my_mvpolynomial.leading_mon f2
#eval multiset.mon_LCM (my_mvpolynomial.leading_mon f1).iget (my_mvpolynomial.leading_mon f2).iget
#eval s_monomial_r f1 f2
#eval s_monomial_r f1 f3
#eval s_monomial_r f2 f3

--(LCM(LM1, LM2) / LT1) * 1
--(take monomaial and coef and make poly) * pol1
def s_polynomial_l (pol1 pol2: my_mvpolynomial σ α) : my_mvpolynomial σ α := 
  (finsupp.single (s_monomial_l pol1 pol2) (1 / (my_mvpolynomial.leading_coef pol1))) * pol1

#eval s_polynomial_l f1 f2
#eval s_polynomial_l f1 f3
#eval s_polynomial_l f2 f3

--(LCM(LM1, LM2) / LT2) * 2
def s_polynomial_r (pol1 pol2: my_mvpolynomial σ α) : my_mvpolynomial σ α := 
  (finsupp.single (s_monomial_r pol1 pol2) (1 / (my_mvpolynomial.leading_coef pol2))) * pol2

#eval s_polynomial_r f1 f2
#eval s_polynomial_r f1 f3
#eval s_polynomial_r f2 f3

-- S-Pol
-- S(pol1,pol2) = s_polynomial_l - s_polynomial_r
def s_polynomial (pol1 pol2: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  (s_polynomial_l pol1 pol2) - (s_polynomial_r pol1 pol2)

#eval s_polynomial f1 f2
#eval s_polynomial f1 f3
#eval s_polynomial f2 f3

--pol2 = num, pol1 = den
--gives which mon from pol2 can be divided with lm(pol1) 
def divide_witness (pol_d pol_n : my_mvpolynomial σ α) : option (multiset σ) :=
  let lmp1 := (my_mvpolynomial.leading_mon pol_d).iget in
  list.find (λ s2, ∀ s ∈ lmp1, (lmp1).count s ≤ (s2: multiset σ).count s) ((finsupp.support pol_n).sort multiset.lex)

--make multiset from divide_witness a polynomial 
def divide_witness_pol (pol_d pol_n : my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  match divide_witness pol_d pol_n with
  | some ms := finsupp.single ms (pol_n.to_fun ms)
  | none := 0
end

-- n/d, q = 0, r = n, 
--while divides tt, t = (C(r) / LC(d)) * (M(r) / LM(d))
--              q = q + t, 
--              r = r - t * d  

def find_pol_t (pol_r pol_d: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  let dw := (divide_witness pol_d pol_r).iget in 
  finsupp.single (dw - (my_mvpolynomial.leading_mon pol_d).iget) 
  ((divide_witness_pol pol_d pol_r).coef dw / my_mvpolynomial.leading_coef pol_d)

--pol_n = pol_d * q + r -> pol_n/pol_d = q + (r / pol_d)
def find_new_q (pol_r pol_d pol_q: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  (pol_q + find_pol_t pol_r pol_d)
  
def find_new_r (pol_r pol_d: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  pol_r - (find_pol_t pol_r pol_d) * pol_d

-- def smaller (pp1 pp2: my_mvpolynomial σ α) : bool :=
--   (((pp1.leading_mon α σ).iget).sort (≥) < ((pp2.leading_mon _ _).iget).sort (≥)) 
  
-- #eval smaller _ _ f1 f2

variables (σ α)
def wf_rel : (Σ' n : my_mvpolynomial σ α, list(my_mvpolynomial σ α)) → 
(Σ' n : my_mvpolynomial σ α , list (my_mvpolynomial σ α)) → Prop := 
  λ m1 m2, 
  ((m2.1.leading_mon).iget).sort (≥) < ((m1.1.leading_mon).iget).sort (≥)

#check wf_rel _ _
-- #check @well_founded _

lemma wf_rel_wf : well_founded (wf_rel α σ) := sorry 

variables {σ α}
def long_div: my_mvpolynomial σ α -> list (my_mvpolynomial σ α) -> my_mvpolynomial σ α
| pol_n (h::t) :=
    have h1 : wf_rel α σ ⟨find_new_r pol_n h, h::t⟩ ⟨pol_n, h::t⟩, from sorry,
    have h2 : wf_rel α σ ⟨pol_n, t⟩ ⟨pol_n, h::t⟩, from sorry,
    if (divide_witness h pol_n) = none then long_div pol_n t 
    else long_div (find_new_r pol_n h) (h::t)
| pol_n [] := pol_n
using_well_founded {rel_tac := λ α σ, `[exact ⟨wf_rel α σ, wf_rel_wf α σ⟩], dec_tac := `[assumption]}

#eval long_div (s_polynomial f1 f2) [f1,f2]
#eval long_div (s_polynomial f2 f2) [f1,f2,f3,f4]
#eval long_div (s_polynomial f3 f3) [f1,f2,f3,f4]
#eval long_div (s_polynomial f4 f4) [f1,f2,f3,f4]
#eval long_div (s_polynomial f1 f3) [f1,f2,f3]
#eval long_div (s_polynomial f1 f3) [f1,f2,f3]
#eval long_div (s_polynomial f2 f3) [f1,f2,f3]
#eval long_div (s_polynomial f2 f4) [f1,f2,f3,f4]
#eval long_div (s_polynomial f3 f4) [f1,f2,f3,f4]
#eval long_div (0) [f1,f2,f3,f4]

------------------------------- Definition Ideal.---------------------- 
-- A subset I ⊂ k[x1, . . . , xn] is an ideal if it satisfies:
-- (i) 0 ∈ I .
-- (ii) If f, g ∈ I , then f + g ∈ I .
-- (iii) If f ∈ I and h ∈ k[x1, . . . , xn], then h f ∈ I .

------------------------------------- Lemma -----------------------------
-- If f1, . . . , fs polynomials in k[x1, . . . , xn], then ⟨f1, . . . , fs⟩ is an ideal of
-- k[x1, . . . , xn]. We call ⟨f1,...,fs⟩ the ideal generated by f1,...,fs

--a basis G = {g1,...,gt} for I ≠ pol_zero  is a gb if ∀ pairs i ≠ j the remainder of S(gi, gt) / G (use my long_div) == 0   
def bb_criterion (basis: list (my_mvpolynomial σ α)) : bool := 
  ∀ x ∈ basis, ∀ y ∈ basis, x ≠ y -> (long_div (s_polynomial x y) (basis) = 0)

--let I a pol ideal ≠ 0. then a gb for I can be constructed in a finite n of steps by the alg:
--1 input is an I = <f1, ... ,fs>
--2 output a GB, G = (g1, . . . , gt) for I , with F ⊂ G
--3 take input, F = (f1,...,fs). ∀ pairs i ≠ j, if remainder of S_pol is ≠ 0, add it to F

--check case where s_pol = 0, also should be r = 0
-- G := F
-- REPEAT
-- G := G
-- FOR each pair {p,q}, p 	= q in G DO
-- S := S(p,q)G
-- IF S 	= 0 THEN G := G ∪ {S}
-- UNTIL G = G

-- def smaller (pp1 pp2: my_mvpolynomial σ α) : bool :=
--   (((pp1.leading_mon _ _).iget).sort (≥) ≤ ((pp2.leading_mon _ _).iget).sort (≥)) 

--every nonzero ideal I ⊂ k[x1, . . . , xn] has a Groebner basis
--(h: my_ideal ≠ zero_ideal α σ)

meta def bb_alg_ax: list(my_mvpolynomial σ α) -> list (my_mvpolynomial σ α) 
| [] := []
| (h::t) := 
    ((h::t) : list (my_mvpolynomial σ α)).foldr(λ p l, 
    (((h::t): list (my_mvpolynomial σ α)).foldr(λ p1 l1, 
    let remainder := (long_div (s_polynomial p p1) (h::t)) in  
        if (remainder ≠ 0 ∧ remainder ∉ ((h::t) : list (my_mvpolynomial σ α)))
          then bb_alg_ax ((h::t) ++ [remainder])
        else l1))
    (l)) 
    (h::t)

meta def bb_alg: list(my_mvpolynomial σ α) -> list (my_mvpolynomial σ α)
| [] := [] 
| [zero_ideal] := []
| (h::t) := 
  bb_alg_ax (h::t) 

#eval bb_alg [f1, f2]
#eval bb_alg [g1,g2,g3]
#eval bb_criterion [f1,f2,f3,f4]
#eval bb_criterion [f1,f2]
#eval bb_criterion [g1,g2,g3,g4]

