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
  m1.sort (≤) ≤ m2.sort (≤)

  instance (m1 m2 : multiset σ) : decidable (multiset.lex m1 m2) := by unfold multiset.lex; apply_instance

example : linear_order (list σ) := by apply_instance

#check @multiset.mem_sort

lemma multiset.sort_ext {m1 m2 : multiset σ} : m1 = m2 ↔ m1.sort(≤) = m2.sort(≤) :=
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

-- def drle (σ : Type) [decidable_linear_order σ] :  
--   decidable_rel (multiset.lex : multiset σ → multiset σ → Prop) :=
-- begin
--   intros a b,
--   apply_instance
-- end

example (σ) [decidable_linear_order σ]: 
∀ a b : σ , decidable (a ≤ b) :=--decidable_rel ((≤) : multiset σ → multiset σ → Prop) :=
 by apply_instance 

#check @multiset.lex_is_total

example (σ) [decidable_linear_order σ]: 
∀ a b : σ , decidable (a ≤ b) :=--decidable_rel ((≤) : multiset σ → multiset σ → Prop) :=
 by apply_instance 

def my_mvpolynomial (σ : Type*) (α: Type*) [comm_semiring α] := 
  finsupp (multiset σ) α

variables (α : Type u) (σ : Type*) [decidable_linear_order σ] [discrete_linear_ordered_field α] {a : α}

--to mame * between my_mvpolynomials
instance : comm_ring (my_mvpolynomial σ α) := finsupp.to_comm_ring

variables (sss ssd: multiset σ)
variables (pip: my_mvpolynomial σ α )
#check multiset.lex sss ssd
#check (finsupp.support pip)

#check  my_mvpolynomial
#check @my_mvpolynomial
example : linear_order (multiset σ) := by apply_instance
example : partial_order (multiset σ) := by apply_instance

variables (ms1 ms2: multiset σ) (mvp: my_mvpolynomial σ α)

def my_mvpolynomial.coef (pol : my_mvpolynomial σ α) := 
  pol.to_fun

#check @my_mvpolynomial.coef
#check my_mvpolynomial.coef α σ mvp

variable (pol: my_mvpolynomial σ α)

#check finsupp.support pol
#check @finset.max

--DEGREE of MONOMIAL
def monomial_degree (ms: multiset σ) : ℕ :=
  multiset.card ms

def my_mvpolynomial.leading_mon (pol: my_mvpolynomial σ α ) := (finsupp.support pol).max
-- def my_mvpolynomial.leading_mon (pol: my_mvpolynomial σ α ):multiset σ:= 
--   match (my_mvpolynomial σ α) with
--   | some pol := (finsupp.support pol).max
--   | none := 0

def degree_LM (pol: my_mvpolynomial σ α) : ℕ := 
  monomial_degree σ ((my_mvpolynomial.leading_mon α σ pol).iget)

def is_zero (pol : my_mvpolynomial σ α) : bool :=
  pol = 0

def zero_ideal := ([0]: list (my_mvpolynomial σ α)) 
#check zero_ideal α σ 
variables (polt1 polt2: my_mvpolynomial σ α)
#check monomial_degree
#check ((my_mvpolynomial.leading_mon _ _ polt1).iget)
#check @my_mvpolynomial.leading_mon
#check my_mvpolynomial.leading_mon _ _ polt1

#check @my_mvpolynomial.coef
#check @option.iget

--def my_mvpolynomial.leading_coef := pol.coef _ _ (leading_mon _ _ pol).iget
def my_mvpolynomial.leading_coef (pol: my_mvpolynomial σ α ): α :=
  match (my_mvpolynomial.leading_mon _ _ pol) with
  | some ms := pol.coef _ _ ms
  | none := 0
end 
#check my_mvpolynomial.leading_coef α σ pol

-----LEADING TERM
def my_mvpolynomial.l_t (pol: my_mvpolynomial σ α ) : my_mvpolynomial σ α :=
  finsupp.single (my_mvpolynomial.leading_mon _ _ pol).iget (my_mvpolynomial.leading_coef _ _ pol) 

--representation of the palynomial
def my_mvpolynomial.repr [has_repr σ] [has_repr α] (p : my_mvpolynomial σ α) : string :=
  if p = 0 then "0" else ((finsupp.support p).sort multiset.lex).foldr 
  --(λ s ms, s ++ "+" ++ ((ms).sort (≤)).foldl (λ s2 s1, s2 ++ repr s1 ++ ",") "") ""
    (λ ms s, s ++ repr (p.to_fun ms)  ++ repr ms ++ if (p.to_fun ms) ≥ 0 then  " + " else " ") ""

instance [has_repr σ] [has_repr α] : has_repr (my_mvpolynomial σ α) :=
 ⟨my_mvpolynomial.repr α σ⟩

#check polt1.l_t _ _
#check multiset.lex (my_mvpolynomial.leading_mon _ _ (polt1.l_t _ _)).iget (my_mvpolynomial.leading_mon _ _ (polt2.l_t _ _)).iget
#check (my_mvpolynomial.leading_mon _ _ (polt1.l_t _ _)).iget

--used in for LCM of monomials 
def multiset.add_repeats (ms: multiset σ) (aa : σ) (n: nat) := (multiset.repeat aa n) + ms
#check @multiset.add_repeats
#eval multiset.add_repeats _ ({} : multiset ℕ) 2 5

--finds LCM of LM1 LM2, outputs in diff order
--for every x add to {} the max repetitions from m1 m2  
def multiset.mon_LCM (m1 m2 : multiset σ) :=
  ((m1.to_finset) ∪ (m2.to_finset)).fold multiset.add ({}) 
  (λ x, multiset.add_repeats _ ({} : multiset σ) x (max (multiset.count x m1) (multiset.count x m2)))

#check multiset.mon_LCM
#eval multiset.mon_LCM _ ({3,3,2} : multiset ℕ) ({2,2, 8} : multiset ℕ)






def ppp: my_mvpolynomial ℕ ℚ :=
  finsupp.single {3,3} 1 -  
  finsupp.single {2} 1

def ppp2: my_mvpolynomial ℕ ℚ :=
  finsupp.single {3,3,3} 1 -  
  finsupp.single {1} 1


--ok
--LCM(LM1, LM2) / LM1
def s_monomial_l (pol1 pol2: my_mvpolynomial σ α): multiset σ :=
  let lmp1 := (my_mvpolynomial.leading_mon _ _ pol1).iget in 
  (multiset.mon_LCM _ lmp1 (my_mvpolynomial.leading_mon _ _ pol2).iget) - lmp1

#eval s_monomial_l _ _ ppp ppp2

--LCM(LM1, LM2) / LM2
def s_monomial_r (pol1 pol2: my_mvpolynomial σ α): multiset σ :=
let lmp2 := (my_mvpolynomial.leading_mon _ _ pol2).iget in 
  (multiset.mon_LCM _ (my_mvpolynomial.leading_mon _ _ pol1).iget lmp2) - lmp2

#eval s_monomial_r _ _ ppp ppp2

--(LCM(LM1, LM2) / LT1) * 1
def s_polynomial_l (pol1 pol2: my_mvpolynomial σ α) : my_mvpolynomial σ α := 
  --(take monomaial and coef and make poly) * pol1
  (finsupp.single (s_monomial_l _ _ pol1 pol2) (1 / (my_mvpolynomial.leading_coef _ _ pol1))) * pol1

#eval s_polynomial_l _ _ ppp ppp2

--(LCM(LM1, LM2) / LT2) * 2
def s_polynomial_r (pol1 pol2: my_mvpolynomial σ α) : my_mvpolynomial σ α := 
  (finsupp.single (s_monomial_r _ _ pol1 pol2) (1 / (my_mvpolynomial.leading_coef _ _ pol2))) * pol2

#eval s_polynomial_r _ _ ppp ppp2

-- S-Pol
-- S(pol1,pol2) = s_polynomial_l - s_polynomial_r
def s_polynomial (pol1 pol2: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  (s_polynomial_l _ _ pol1 pol2) - (s_polynomial_r _ _ pol1 pol2)

#eval s_polynomial _ _ ppp ppp2

--what is in denom must be contained also in num
def divides' (ms1 ms2 : multiset ℕ) : bool := 
  ∀ ⦃a : ℕ⦄, a ∈ ms1 → a ∈ ms2 

def divides'' (lm: multiset ℕ) (mms2: multiset (multiset ℕ)) : bool := 
  ∃ s2 ∈ (mms2), ∀ n ∈ lm, lm.count n ≤ (s2 : multiset ℕ).count n

--there is some monomial in pol1 that is a multiple of lm(pol2)
--{1,1} divides {1,1,1,1}
def divides (pol1 pol2 : my_mvpolynomial σ α) : bool := 
  ∃ s2 ∈ (finsupp.support pol2), ∀ ⦃s : σ⦄, (s ∈ (my_mvpolynomial.leading_mon _ _ pol1).iget  →  s ∈ s2)

#eval divides' {2} {1,2}
#eval divides' {1,1,3,3,3} {1,3,3,1,2} 
#eval divides'' {1,1,7,2} {{1,1,1,5,5,7,2},{2},{}}
#eval divides'' {1,1,7,2} {{1,1},{7,2}}
#eval divides'' {1,1} {{1}}
#eval divides'' {1} {{1, 1}}
#check divides _ _ pol pol
#check finsupp.support pol
#check (finsupp.support pol).max.iget
#check (my_mvpolynomial.leading_mon _ _ pol).iget

-------------------------------------------------------------------------
def divide_witness' (l1: list ℕ) (l2 : list (list ℕ)) : option (list ℕ) :=
  list.find (λ s2, ∀ s ∈ l1, l1.count s ≤ (s2 : list ℕ).count s) l2

--pol2 = num, pol1 = den
--gives which mon from pol2 can be divided with lm(pol1) 
def divide_witness (pol_d pol_n : my_mvpolynomial σ α) : option (multiset σ) :=
  let lmp1 := (my_mvpolynomial.leading_mon _ _ pol_d).iget in
  list.find (λ s2, ∀ s ∈ lmp1, (lmp1).count s ≤ (s2: multiset σ).count s) ((finsupp.support pol_n).sort multiset.lex)

--make multiset from divide_witness a polynomial 
def divide_witness_pol (pol_d pol_n : my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  match divide_witness _ _ pol_d pol_n with
  | some ms := finsupp.single ms (pol_n.to_fun ms)
  | none := 0
end

#eval list.count 3 [1,5,3,2]
#eval divide_witness' [1,1] [[2,3],[1,2],[1],[1,1]]
#eval divide_witness' [1,1,1] [[2,3],[1,2,1],[1],[1,1,2,3,1]]
#check (my_mvpolynomial.leading_mon _ _ pol).iget
#check (finsupp.support pol).sort multiset.lex
#check finsupp.support pol
#check @multiset.lex_is_total σ 
#check @finset.sort
#check (finsupp.support pol).sort multiset.lex
#check divide_witness_pol _ _ pol pol


-- n/d, q = 0, r = n, 
--while divides tt, t = (C(r) / LC(d)) * (M(r) / LM(d))
--              q = q + t, 
--              r = r - t * d  

-- def find_pol_t (pol_r pol_d: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
--   finsupp.single ((divide_witness _ _ pol_d pol_r).iget - (my_mvpolynomial.leading_mon _ _ pol_d).iget) 
--   ((divide_witness_pol _ _ pol_d pol_r).coef _ _ (divide_witness _ _ pol_d pol_r).iget / my_mvpolynomial.leading_coef _ _ pol_d)

def find_pol_t (pol_r pol_d: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  let dw := (divide_witness _ _ pol_d pol_r).iget in 
  finsupp.single (dw - (my_mvpolynomial.leading_mon α σ pol_d).iget) 
  ((divide_witness_pol _ _ pol_d pol_r).coef _ _ dw / my_mvpolynomial.leading_coef _ _ pol_d)

--pol_n = pol_d * q + r -> pol_n/pol_d = q + (r / pol_d)
def find_new_q (pol_r pol_d pol_q: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  (pol_q + find_pol_t _ _ pol_r pol_d)
  --if pol_q = none then find_pol_t _ _ pol_r pol_d else pol_q.iget + find_pol_t _ _ pol_r pol_d 

def find_new_r (pol_r pol_d: my_mvpolynomial σ α) : my_mvpolynomial σ α :=
  pol_r - (find_pol_t _ _ pol_r pol_d) * pol_d

--div_pol performs the division until no longer possible. outputs remainder only. 
--for complete division must do pol_n/pol_d = q + r/pol_d    
-- section divide
-- meta def div_pol : my_mvpolynomial σ α → my_mvpolynomial σ α →  my_mvpolynomial σ α 
-- | pol_n pol_d :=
--   if h:(divide_witness _ _ pol_d pol_n) = none then pol_n else
--    let r := (find_new_r _ _ pol_n pol_d) in div_pol r pol_d
-- end divide
-- --rerun until no
-- #check div_pol _ _ pol pol

-- divide a pol with list of pols
-- must assume list is ordered
meta def long_div: my_mvpolynomial _ _ -> list (my_mvpolynomial _ _) -> my_mvpolynomial σ α
  | pol_n (h::t) := if (divide_witness α σ h pol_n) = none then long_div pol_n t else
    long_div (find_new_r α σ pol_n h) (h::t)
  | pol_n [] := pol_n

#check long_div α σ pol [pol,pol]

--nil?????????????????
--must add 0/x = 0
--should make a prop about basis
--every ideal other than 0 has a basis

------------------------------- Definition Ideal.---------------------- 
-- A subset I ⊂ k[x1, . . . , xn] is an ideal if it satisfies:
-- (i) 0 ∈ I .
-- (ii) If f, g ∈ I , then f + g ∈ I .
-- (iii) If f ∈ I and h ∈ k[x1, . . . , xn], then h f ∈ I .

------------------------------------- Lemma -----------------------------
-- If f1, . . . , fs polynomials in k[x1, . . . , xn], then ⟨f1, . . . , fs⟩ is an ideal of
-- k[x1, . . . , xn]. We call ⟨f1,...,fs⟩ the ideal generated by f1,...,fs

--a basis G = {g1,...,gt} for I ≠ pol_zero  is a gb if ∀ pairs i ≠ j the remainder of S(gi, gt) / G (use my long_div) == 0   
meta def bb_criterion (basis: list (my_mvpolynomial σ α)) : bool := 
  ∀ x ∈ basis, ∀ y ∈ basis, x ≠ y -> (long_div _ _ (s_polynomial α σ x y) (basis) = 0)
#check bb_criterion α σ [pol]

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

-- meta def bb_alg' (my_ideal: list (my_mvpolynomial σ α)) : list(my_mvpolynomial σ α) :=
--   my_ideal.foldl (λ l n, my_ideal.foldl (λ l' m, if long_div α σ (s_polynomial α σ m n) (my_ideal) ≠ 0 
--   then (long_div α σ (s_polynomial α σ m n) (my_ideal)::l') else l') l) my_ideal

--every nonzero ideal I ⊂ k[x1, . . . , xn] has a Groebner basis
meta def bb_alg (my_ideal: list (my_mvpolynomial σ α)) (h: my_ideal ≠ zero_ideal α σ) : list(my_mvpolynomial σ α) :=
  my_ideal.foldl (λ l n, my_ideal.foldl (λ l' m, 
  let remainder := (long_div α σ (s_polynomial α σ m n) (my_ideal)) in 
  if remainder ≠ 0 then (if remainder ∉ l' then remainder::l' else l') else l') l) my_ideal

#check bb_alg α σ [pol,pol]
#check bb_alg α σ [pol]
--#check bb_alg' α σ [pol]
#check @bb_alg
--#check @bb_alg'


------------------------------- cannot ------------------
-- meta example (basis : list (my_mvpolynomial σ α)) : bb_criterion α σ (bb_alg' α σ (basis)) = tt :=
-- begin
--   simp*
-- end
-- lemma bb_is_gb: ∀ basis : list (my_mvpolynomial σ α), bb_criterion α σ (bb_alg' α σ (basis)) = tt :=
-- begin
--     intro basis,
--     cases basis with pol list_pol,
--     unfold bb_criterion
-- end

#check long_div α σ pol [pol,pol]
#eval nat.div 0 0
#check finsupp.map_domain
variables p q : my_mvpolynomial σ α 
variables pp qq : multiset σ
variables (as ad af : σ)
#check p
#check (1 / (my_mvpolynomial.leading_coef _ _ p))
#check s_monomial_l _ _ p q
#check multiset.mon_LCM _ (my_mvpolynomial.leading_mon _ _ p).iget (my_mvpolynomial.leading_mon _ _ q).iget
#check p * q
#check s_monomial_l _ _ p q
#check my_mvpolynomial.l_t _ _ p
#check pp + qq
#check pp - qq
#check p - q
#check p * q
--#check p / q
#eval ({1, 1, 1, 2, 2} : multiset ℕ) - {1, 1, 2}
#check (my_mvpolynomial.leading_coef α σ pol / my_mvpolynomial.leading_coef α σ pol)
#check finsupp.support p
#check s_polynomial α σ p q
#eval ({1, 1, 1, 2} : multiset ℕ) - {1, 1, 2, 5, 6, 9}
#eval multiset.prod ({1, 1, 5, 2} : multiset ℕ)
#check multiset.lex pp qq


def f5 : my_mvpolynomial ℕ ℚ :=
  finsupp.single {2,4} 100 +  
  finsupp.single {1, 1, 2} 20
#eval f5.to_fun {3,2}
variable (mmm: multiset σ)
#check finsupp.single mmm (pol.to_fun mmm)

#check (mmm).sort (≤)
#check (finsupp.support pol).sort multiset.lex
#check (f5 : my_mvpolynomial ℕ ℚ)
#check my_mvpolynomial.repr
#eval my_mvpolynomial.l_t _ _ f5
#check  my_mvpolynomial.l_t _ _ f5
#eval f5

def nom: my_mvpolynomial ℕ ℚ :=
  finsupp.single {1,1,1} 1 -  
  finsupp.single {1,1} 12 - 42 

def denom: my_mvpolynomial ℕ ℚ :=
  finsupp.single {1,1} 1 -  
  finsupp.single {1} 2 + 1

  
#eval long_div _ _ nom [denom]