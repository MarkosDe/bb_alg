structure point (α : Type) :=
    mk :: (x : α) (y : α)

#reduce point.x (point.mk 10 20) --10
#reduce point.y (point.mk 10 20) --20

example (α : Type) (a b : α) : point.x (point.mk a b) = a :=
begin
    --simp
    refl
end

def p := point.mk 10 20
#reduce p.x  --10

namespace point
def add (p q : point ℕ) := 
    mk (p.x + q.x) (p.y + q.y)
end point

def t : point ℕ := point.mk 1 2
def q : point ℕ := point.mk 3 4
#reduce t.add q


-------make it polymorphic by:----------------------
--declaring a universe variable on the fly
structure {v} point2 (α : Type v) :=
    mk :: (x : α) (y : α)
--or using underscore   
structure point3 (α : Type _) :=
    mk :: (x : α) (y : α)
#check @point
#check @point2
#check @point3

----------------------------OBJECTS-------------------------------------------------------
/- For structures containing many fields we have to remember the order in which the fields 
were defined = problem -/
#check { point . x := 10, y := 20 } --or
#check { point . y := 20, x := 10 } --or
#check ({x := 10, y := 20} : point ℕ)

--------------------------INHERITANCE--------------------------------
--extend existing structures by adding new fields
structure points (α : Type) :=
    (x : α) (y : α) (z : α)
structure rgb_val :=
    (red : nat) (green : nat) (blue : nat)
structure red_green_point (α : Type) extends points α, rgb_val :=
    (no_blue : blue = 0)
def l : points (nat) := 
    {x := 10, y := 10, z := 20}
def rgp : red_green_point (nat) :=
    {red := 200, green := 40, blue := 0, no_blue := rfl, ..l}

example : rgp.x = 10 := rfl
example : rgp.red = 200 := rfl