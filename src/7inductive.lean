---------------enumerated types---------------
inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

#check weekday.sunday
open weekday
#check sunday

def number_of_day (d : weekday) : nat :=
weekday.rec_on d 1 2 3 4 5 6 7
#reduce number_of_day weekday.sunday
#reduce number_of_day weekday.monday
#reduce number_of_day weekday.tuesday

namespace weekday
    def next (d : weekday) : weekday :=
        weekday.rec_on d monday tuesday wednesday thursday friday
        saturday sunday
    def previous (d : weekday) : weekday :=
        weekday.rec_on d saturday sunday monday tuesday wednesday
        thursday friday
    #reduce next tuesday
    #reduce next (next tuesday)
    #reduce next (previous tuesday)
    --example : next (previous tuesday) = tuesday := rfl
end weekday

namespace weekday
    theorem next_previous (d: weekday) : next (previous d) = d := 
    --weekday.rec_on d rfl rfl rfl rfl rfl rfl rfl
    by apply weekday.rec_on d; refl
end weekday

---------constructors with arguments-----------

-- αυτο στο inductive του βαζεις ονομα και καλεις 
-- με δυο διαφορετικα οπως στις υπολοιπες γλωσσες

--def double (x : nat) : nat := x + x
def double: nat -> nat := λx, x + x 

universes u v w
inductive My_prod (α : Type u) (β : Type v)
| mk : α -> β -> My_prod                --mk is default name

--open My_prod
--#eval double 3
def My_fst {α: Type u} {β : Type v} (p : My_prod α β) : α :=  --solved
    My_prod.rec_on p (λ a b, a)  


variables (t er yt tr: Type u)(o: Type v)
#reduce My_fst (My_prod.mk 1 t)
#reduce My_fst ⟨1, t⟩ -----------------------------

--#eval fst (1, t, er, yt, 5, o) --error?
--if tt double, if ff double + 1
---------------------------------------------------------------------------------------
def prod_example (p : bool × ℕ) : ℕ :=
    prod.rec_on p (λ c n, cond c (2 * n) (2 * n + 1))  
         
#eval prod_example (tt, 3)
#eval prod_example (ff, 3)
#reduce prod_example (ff, 3)


def prod_example1 (p : My_prod bool ℕ) : ℕ :=
    My_prod.rec_on p (λ c n, cond c (2 * n) (2 * n + 1))  
#eval prod_example1 ⟨ tt, 3⟩
#eval prod_example1 (My_prod.mk ff 3)

--bool and the result of double
variable (b: ℕ)
def prod_example2 (p : bool × ℕ) : ℕ :=
    prod.rec_on p (λ c b, cond c (2 * double b) (2 * double b + 1))     ---

#eval prod_example2 (ff, 3)
#reduce prod_example2 (ff, 3)


--what if I want bool and the result of fst(with 2 arguments) -------------
def prod_example3 {β : Type v} {γ : Type v} (b : My_fst ⟨β, γ⟩) (p : bool × ℕ) : ℕ :=
    prod.rec_on p (λ c b, cond c (2 * b) (2 * b + 1))

#reduce prod_example3 (ff, (3, 8)) 
--#eval prod_example3 (ff, (3, 8, 7)) 
#check prod_example3

--------------------example 2-----------------
--{} makes the argument implicit by deafault
-- works also without {}, difference ???????
inductive My_sum (α : Type u) (β : Type v)
| inl : α -> My_sum      --insert left  
| inr : β -> My_sum      --insert right

def sum_example (s: ℕ ⊕ ℕ) : ℕ :=
    sum.cases_on s (λ n, 2 * n) (λ n, 2 * n + 1) --not My_sum?
#check @My_sum.inl
#eval sum_example (sum.inl 4)
#eval sum_example (sum.inr 4)

---what if sum_example with 3 cases???????????????
inductive My_sum1 (α : Type u) (β : Type v) (γ: Type w)
| inl {} : α -> My_sum1      --insert left  
| inr {} : β -> My_sum1      --insert right
--| inm {} : γ -> My_sum1

def sum_example2 (s: ℕ ⊕ ℕ) : ℕ :=
    sum.cases_on s (λ n, 2 * n) (λ n, 2 * n + 1)  --not My_sum?



---------------structure-----------
section colour
    structure color := (red : nat) (green : nat) (blue : nat)
    def yellow := color.mk 255 255 0

    #reduce color.red yellow
    #eval color.red yellow
end colour


namespace nat
    def add' (m n : nat) : nat :=
    nat.rec_on n m (λ n add_m_n, succ add_m_n)
    #reduce add' (succ zero) (succ (succ zero))
end nat

theorem add_zero' (m : nat) : m + 0 = m := 
begin
--apply refl
apply add_zero m
end

inductive nat' : Type
| zero : nat'
| succ : nat' -> nat'
#check @nat'.rec_on

open nat'
example (n : ℕ) (h : n ≠ 0) : nat.succ (nat.pred n) = n := ------????
begin
    cases n with m,
    { apply (absurd rfl h) },
    reflexivity
end


constants p q : Prop
theorem t1 : p -> q -> p :=
begin
    assume hp : p,
    assume hq : q,
    --exact hp
    show p, from hp
end

theorem add_succ' (m n : nat) : m + nat.succ n = nat.succ (m + n) := 
begin
apply rfl
end

theorem zero_add' (n : ℕ) : 0 + n = n :=
begin
from nat.rec_on n rfl (λ n ih, by rw [add_succ', ih])
end
-----------------Other----------------

inductive list' (α : Type u)
| nil {} : list'
| cons : α -> list' -> list'

#check (list'.cons 1(list'.cons 5.3(list'.nil)) : list' nat)   --------
#check ([1, 5, 6] : list int)

variable (α: Type u)
theorem append_nil (t : list α) : t ++ [] = t := 
begin
    induction t,
    reflexivity,
    rw list.cons_append,
    rw t_ih 
    --by simp        
end

theorem append_nil' : ∀ (t : list α), t ++ [] = t 
| [] := rfl
| (h::t) := by rw [list.cons_append, append_nil'] 


theorem append_assoc (r s t : list α) : r ++ s ++ t = r ++ (s ++ t) :=
begin
    rw list.append_assoc
    --by simp
end


-----defining the function length
def length': Π {α : Type u}, list α → nat   
| _ [] := 0                 ---im recursing on α so must say wahtatype (_)
| α (h :: t) := length' t + 1


def length'' {α : Type u}: list α → nat
| [] := 0
| (h :: t) := length'' t + 1

def max'' {α : Type u} : list ℕ -> ℕ
| [] := 0
| [m] := m
| [h, t] := if h ≤ t then t else h
| (h::m::t) := if h ≤ m then max'' (m::t) else max'' (list.cons h t)

#eval list.insert 5 [1,2,3] 
#reduce max'' ([66,1,2,3,4,8,5,5,3,2,4,9] : list ℕ)
#eval list.insert 3 [1,4,5]
#eval list.erase [1,2,3] 2
#eval list.cons 3 [4,5]
def tail1'' {α : Type u} : list α -> list α
| [] := []
| [m] := [m] 
| (h :: t) := tail1'' t
#eval tail1'' [5,7]
#eval tail1'' [5,7,4,1,2]


def f (n : ℕ) : ℕ :=
begin
    cases n, 
    exact 3, 
    exact 7
end
example : f 0 = 3 := 
begin
    reflexivity
end
example : f 5 = 7 := 
begin
    reflexivity
end

inductive foo : Type
| bar1 : ℕ -> ℕ -> foo
| bar2 : ℕ -> ℕ -> ℕ -> foo

def silly (x : foo) : ℕ :=
begin
    cases x,
    case foo.bar1 : a b { exact b },
    case foo.bar2 : c d e { exact e }
end

open nat
variable p : ℕ -> Prop
example (hz : p 0) (hs : forall n, p (succ n)) (m k : ℕ) : p (m + 3 * k) :=
begin
-- cases (m + 3 * k),
-- { exact hz }, -- goal is p 0
-- apply hs -- goal is a : N ⊢ p (succ a)

generalize : m + 3 * k = n,
cases n,
{ exact hz }, -- goal is p 0
apply hs -- goal is a : N ⊢ p (succ a)
end

#check nat.sub_self
example (m n : ℕ) : m - n = 0 ∨ m ≠ n :=
begin
    cases decidable.em (m = n) with heq hne,
    { rw heq,
    left, exact nat.sub_self n },
    right, exact hne
end

---------use the case split in a computable function----------------
def ft (m k : ℕ) : ℕ :=
begin
    cases m - k, --cases tactic can be used to carry out proof by cases
    exact 2, 
    exact 7
end
example : ft 10 15 = 2 := rfl
example : ft 10 2 = 7 := rfl

theorem zero_add'' (n : ℕ) : 0 + n = n :=
begin
/- Assuming x is a variable in the local context with an inductive type, 
induction x applies induction on x to the main goal, 
producing one goal for each constructor of the inductive type, -/
    induction n,
    case nat.zero : { refl },
    case nat.succ : p ih { rw [add_succ, ih]}
end

theorem succ_add (m n : ℕ) : nat.succ m + n = nat.succ (m + n) :=
begin
    induction n,
    case nat.zero : { refl },
    case nat.succ : s re { rw [add_succ, re] }
end

------------------Injection----------------------
open nat
example (m n k : ℕ) (h : succ (succ m) = succ (succ n)) :
n + k = m + k :=
begin
injection h with h',
injection h' with h'',
--injections with h' h'',
--simp [h'']
rw h''
end

--also detects contraddictions
example (m n : ℕ) (h : succ m = 0) : n = n + 7 :=
begin
injection h
--contradiction
end

---------------7.7 families-----------
inductive eq' {α : Sort u} (a : α) : α -> Prop  ??????
| refl : eq' a
