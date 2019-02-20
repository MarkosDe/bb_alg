import init.algebra.ordered_ring
import init.algebra.ring
import init.data.set
import data.polynomial
import ring_theory.ideals data.nat.choose order.zorn
import algebra.module
open set
open ring
open polynomial
#check module

universes u
variables {α : Type u} [comm_ring α] {a : α} {m n : ℕ}
variables [decidable_eq α]{p q r: polynomial α} {i : ideal α}
--def polynomial (α : Type*) [comm_semiring α] := finsupp ℕ α   --ℕ →₀ α

def leading_monomial (p : polynomial α) : α :=  nat_degree p
@[simp] lemma leading_monomial_zero : leading_monomial (0 : polynomial α) = 0 := rfl

-- example : leading_monomial (3*X ^ 5) = 3* X^5 :=
-- begin
  
-- end
example : leading_coeff (1*X ^ 5) = 1  :=
begin
 rw[leading_coeff],
 rw[coeff],
 rw[nat_degree],
 simp*,
 apply coeff_X_one   
end

-- example : leading_coeff (3*X ^ 5) = 3  :=
-- begin
--  rw[leading_coeff],
--  rw[coeff],
--  rw[nat_degree],
--  refl
-- endc

def fhalf {α:Type} (xs:list α): list α :=
    list.take(list.length xs/2) xs

def shalf {α:Type} (xs:list α): list α :=
    list.drop(list.length xs/2) xs

#eval fhalf [2,1,6,3,5]  
#eval shalf [4,5,8] 


def merge: list ℕ -> list ℕ -> list ℕ
| [] xs := xs
| ys [] := ys
| [x] [y] := if x < y then [x,y] else [y,x]
| (x::xs) (y::ys) := if x < y then x::(merge xs (y::ys)) else y :: merge(x::xs) ys

lemma sizeof_my_le {α} [h : has_sizeof α] : ∀ n (xs : list α), 
    list.sizeof (list.take n xs) ≤ list.sizeof xs :=
    begin
        intros n l,
        induction  n,
        induction l,
        simp,
        --calc list.sizeof list.nil ≤ list.sizeof (l_hd :: l_tl) =  1  ≤ list.sizeof (l_hd :: l_tl) : by 
        --assume kl: list.sizeof list.nil,
        simp,
        apply le_add_right,
        show 1 ≤ _,
        simp,
        
        --change list.sizeof (@list.nil α) with 1,
        --simp[list.sizeof list.nil],
        -- apply le_add_right,
        -- apply le_refl,

    end


#eval merge [1,5,7,4][2,3]
#eval merge [5][10]

def mergeSort {a:ℕ} : list ℕ -> list ℕ
|   [] := []
|   [a] := [a]
|   (x::xs) := 
    have suc1: list.sizeof (fhalf xs) < x + (1 + list.sizeof xs), 
        from sorry,
    have suc2 : list.sizeof (shalf xs) < x + (1 + list.sizeof xs), 
        from sorry,
    merge (mergeSort (fhalf xs)) (mergeSort (shalf xs))

--#eval mergeSort 2 [2,1,5,3,4]

def l : list nat := [1, 2, 3]
def f2 : nat -> nat := λ x, x * x
#eval list.map f2 l