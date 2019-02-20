open nat

def sub1' : ℕ -> ℕ
| zero := zero
| (succ x) := x

def is_zero' : ℕ -> Prop
| zero := true
| (succ x) := false

example : sub1' 5 = 4 :=
begin
 refl
end

example (x : ℕ) : sub1' (succ x) = x := 
begin
    refl
end

example : is_zero' 0 = true := 
begin
    refl
end    

example (x : ℕ) : ¬is_zero' (x + 3) := not_false

def sub_1 : ℕ -> ℕ
| 0 := 0
| (x+1) := x
def is_zero1 : ℕ -> Prop
| 0 := true
| (x+1) := false

universes u v
variables {α : Type u} {β : Type v}
def swap_pair : α × β -> β × α
| (a, b) := (b, a)
def foo : ℕ × ℕ -> ℕ
| (m, n) := m + n
def bar : option ℕ -> ℕ
| (some n) := n + 1
| none := 0

#eval swap_pair (5, 4)
#eval foo (5, 4)


open nat
def sub2' : ℕ -> ℕ
| zero := 0
| (succ zero) := 0
| (succ (succ a)) := a

def sub2'' : ℕ -> ℕ
| 0 := 0
| 1 := 0
| (a + 2) := a

example (a : nat) : sub2' (a + 2) = a := rfl
example (a : nat) : sub2'' (a + 2) = a := rfl

def foo' : ℕ × ℕ -> ℕ
| (0, n) := 0
| (m+1, 0) := 1
| (m+1, n+1) := 2

#eval foo' (0,5)
#eval foo' (5,0)
#eval foo' (4,5)

def foo'' : ℕ -> ℕ -> ℕ -> ℕ
| 0 (m+1) 0 := 1
| 0 0 (m+1) := 1
| (m+1) 0 0:= 1
| 0 0 0 := 0
| (m+1) (n+1) 0:= 2
| (m+1) (n+1) (h+1) := 3
| (m+1) 0 (n+1) := 2
| 0 (m+1) (n+1) := 2
#eval foo'' 5 4 6
#eval foo'' 0 1 0
#eval foo'' 5 1 0
#eval foo'' 0 0 0

def bar' : list ℕ -> list ℕ -> ℕ
| [] [] := 0
| (a :: l) [] := a
| [] (b :: l) := b
| (a :: l) (b :: m) := a + b

#eval bar' [2,3] [5,8]
#eval bar' [2,3] []
#eval bar' [] []

def band' : bool -> bool -> bool
| tt a := a
| ff _ := ff

#eval band' tt ff

---α: Type u is a parameter and does not participate in pattern matching so in {}
def tail1' {α : Type u} : list α -> list α
| [] := []
| (h :: t) := t

#eval tail1' [5,7] 
#eval tail1' [5,7,8,7,4,1,2]

------how if [5,7,4,1]?------------------------
def tail1'' {α : Type u} : list α -> list α
| [] := []
| [m] := [m] 
| (h :: t) := tail1'' t
#eval tail1'' [5,7]
#eval tail1'' [5,7,4,1,2]

/- def foo''' : ℕ -> ℕ -> ℕ -> ℕ
| 0 0 0 := 0
| _ _ 0 := 2
| 0 0 _ := 1
| _ _ _ := 3
| _ 0 _ := 2
| _ 0 0 := 1

#eval foo''' 0 0 0
#eval foo''' 5 0 1  -/

variables (a b : ℕ)
def f2 : ℕ -> ℕ -> option ℕ
| 0 _ := some 1
| _ 0 := some 2
| _ _ := none -- the "incomplete" case
example : f2 0 0 = some 1 := rfl
example : f2 0 (a+1) = some 1 := rfl
example : f2 (a+1) 0 = some 2 := rfl
example : f2 (a+1) (b+1) = none := rfl

#eval f2 0 0   --not some 2 cause some 1 is first
#eval f2 1 1

def f1 : ℕ -> ℕ -> ℕ
| 0 _ := 1
| _ 0 := 2
| _ _ := arbitrary ℕ -- the "incomplete" case

#eval f1 1 1
#eval f1 1 9                        --why 0? change 0 into other?

----------structural recursion and induction------------

 /- def add' (m n : nat) : nat :=
    nat.rec_on n m (λ n add_m_n, succ add_m_n -/

def add'' : nat -> nat -> nat
| m zero := m
| m (n+1) := succ (add'' m n)

#eval add'' 0 2

def mul' : nat -> nat -> nat
| n zero := zero
| n (succ m) := mul' n m + n

#eval mul' 2 7

theorem zero_add'' : ∀ n, zero + n = n
| zero := 
    begin
        simp 
    end 
| (succ n) :=
    begin
        simp
    end  

def get_head' {α : Type u}: list α -> α
| [] :=  --empty??????????????????????????????????????????????????????????????
| [n] := n
| (n::m) := n

#eval get_head' [6, 5, 9]

def append'' {α : Type} : list α -> list α -> list α
| [] [] := []
| [] l := l
| (h::t) l := h :: append'' t l

#eval append'' [5,7] [8,9]
#eval append'' [9] []

#eval append'' [(1 : ℕ), 8, 9] [4, 5]