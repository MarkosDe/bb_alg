--import data.list.basic
import data.list.basic


variables (f : ℕ -> ℕ) (k : ℕ)
example (h1 : f 0 = 0) (h2 : k = 0) : f k = 0 :=
/- begin
    rw h2,
    assumption --rw h1
    -- rw [h2, h1]
end -/
begin
    simp * -- [h2,h1]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
by rw[add_assoc, add_comm b, <- add_assoc]

universe u
example {α : Type u} [ring α] (a b c : α) :
a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
begin
rw [mul_zero, mul_zero, zero_mul, zero_mul],
repeat { rw add_zero }
end

section simp
    variables (x y z : ℕ) (e : ℕ -> Prop)
    variable (h : e (x * y))

    example : (x + 0) * (0 + y * 1 + z * 0) = x * y :=
        by simp

    include h
    example : e ((x + 0) * (0 + y * 1 + z * 0)) :=
        begin
            simp,
            exact h --assumption
        end
end simp


universe o
variable {α : Type}
open list
example (xs : list ℕ) : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs :=
    by simp [reverse_core]

example (xs ys : list α) : length (reverse (xs ++ ys)) = length xs + length ys :=
    by simp

section local1
    variables (x y z w : ℕ) (r : ℕ -> Prop)
    local attribute [simp] mul_comm mul_assoc mul_left_comm
    --?
    
    example : x * y + z * w * x = x * w * z + y * x :=
        begin
            simp
        end

    example (h : r (x * y + z * w * x)) : r (x * w * z + y * x) :=
    begin 
        simp, 
        simp at h, 
        assumption 
    end
end local1

def yy (m n : ℕ) : ℕ := m + n + m
example {m n : ℕ} (h : n = 1) (h' : 0 = m) : (yy m n) * m = m :=
begin 
    simp [h, h'.symm, yy]
end

section ex1
    variables (x x' y y' : ℕ)
    example (h1 : x + 0 = x') (h2 : y + 0 = y') : x + y + 0 = x' + y' :=
    begin
        rw add_zero,
        simp at *,
        --simp at h1,
        --simp at h2,
        simp *
    end
end ex1

section ex2
    variables (u w x x' y y' z : ℕ) (p : ℕ -> Prop)
    example (h1 : x = y + z) (h2 : w = u + x) (h3 : p (z + y + u)) : p w :=
    begin
        simp *,
        simp at h3,
        assumption
    end
end ex2


----------------REVERSE------------------
open list
universe i
variables {γ : Type} (x y z : γ) (xs ys zs : list γ)
def mk_symm (xs : list γ) := xs ++ reverse xs
#eval reverse [(1,2),(5,6)]
#eval mk_symm [(1,2),(5,6)]

theorem reverse_mk_symm (xs : list γ ) : reverse (mk_symm xs) = mk_symm xs :=
    by simp [mk_symm]

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
begin
    simp *
end

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
begin
    split,
    simp [hp],
    split,
    simp [hp],
    simp [hp]
end