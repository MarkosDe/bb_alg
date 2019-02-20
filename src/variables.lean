variables (α β γ : Type)
variables (g : β -> γ) (f : α -> β) (h : α -> α)
variable x : α
def compose := g (f x)
def do_twice := h (h x)
def do_thrice := h (h (h x))
#print compose

section suca
def sucami : nat -> nat := λx, x + 1
end suca

#reduce sucami 5

universe u
section
    variable {δ : Type u}
    variable y : δ
    def ident := y
end
variables δ ε : Type u
variables (a : δ) (b : ε)
#check ident
#check ident a
#check ident b

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ x y, f (x, y)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ pair, f pair.1 pair.2