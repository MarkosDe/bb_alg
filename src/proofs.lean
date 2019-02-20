import init.data.list.basic

theorem test (p q : Prop) (hp : p) (hq : q) : p /\ q /\ p :=
begin
    apply and.intro,
    exact hp,
    apply and.intro,
    exact hq,
    exact hp
end

variables (p q : Prop) (hp : p) (hq : q)
example : p /\ q /\ p :=
let hp := hp, hq := hq in
begin
    apply and.intro hp,
    exact and.intro hq hp
end

example (α : Type) : α -> α :=
begin
    intro a,
    exact a
end

example (x : nat) : x ≤ x :=
begin
    refl
end

namespace transitivity0
    variables (x y z : nat)
    --include x y z
    --example (x < y) (y < z): x < z :=
    theorem suca (h1: x < y) (h2: y < z): x < z :=
    begin
    apply trans h1 h2
    end
end transitivity0

namespace transitivity1
    variables (x y z : nat)
    theorem suca (h1: x < y) (h2: y < z): x < z :=
    begin
        transitivity y,
        exact h1,
        exact h2    ----or repeat {assumption}
    end
    #print suca
    #check @suca
end transitivity1

namespace difference
    example (x y : ℕ) (h : x = y) : y = x :=
    begin
        symmetry,
        exact h --or assumption
    end
    
    example (x y : ℕ) (h : x = y) : y = x :=
    begin
        revert x,
        intros,  --what is 
        symmetry,
        assumption
    end
end difference

example : 2 + 3 = 5 :=
begin
    generalize : 3 = x,
    sorry    
end

example (p q : Prop) : p /\ q -> q /\ p :=
begin
    intro h,
    cases h with hp hq,
    constructor,        --?
    repeat {assumption}
end

example (n : nat) : n + 1 = nat.succ n :=
begin
--show nat.succ n = nat.succ n,
reflexivity
end

--tactic - term style
example (p q : Prop) : p /\ q -> q /\ p :=
begin
    intro h,
   -- have hp := h.left,
    --have hq := h.right,
    cases h with hp hq,
    split,
    show p, from hp,    --why show must follow order?
    show q, from hq,    --why not exact hp 
end

example (p q : Prop) (hp : p) (hq : q) : p /\ q :=
begin
    by split; assumption
end