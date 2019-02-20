--def double (x : nat) : nat := x + x
def double: nat -> nat := λx, x + x 
#print "double"
#print double
#check double 3
#reduce double 3
#eval double 3

universe u
constants α β: Type u
#check α
#check β

--def bmiTell : nat -> nat -> nat := λx y, x + y
def sum' (x : nat) (y : nat) : nat := x + y^2
#reduce sum' 8 2

namespace suca
    inductive nat
    | x: nat
    | succ : nat → nat
    #print nat
end suca

def add : nat → nat → nat
| m nat.zero     := m
| m (nat.succ n) := nat.succ (add m n)

#reduce add 5 6

def add' (x:nat)  (y:nat) : nat := x + y
#reduce add' 5 6

def add'' : nat → nat → nat
| m nat.zero     := m
| m (nat.succ n) := nat.succ (add'' m n)
#reduce add (nat.succ nat.zero) (nat.succ nat.zero)

