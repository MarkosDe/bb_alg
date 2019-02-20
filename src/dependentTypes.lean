--the type of the value returned depends on inputnamespace hidden
namespace hidden
universe u
constant list : Type u -> Type u
constant cons : Π α : Type u, α -> list α -> list α
constant nil : Π α : Type u, list α
constant head : Π α : Type u, list α -> α
constant tail : Π α : Type u, list α -> list α
constant append : Π α : Type u, list α -> list α -> list α
end hidden

--difference ?
universe u
constant cons : Π {α : Type u}, α -> list α -> list α
constant con : Π (α : Type u), α -> list α -> list α

constant f : Π {a : ℕ} (b : ℕ), ℕ 


#check cons 2 [1, 2]
#check con ℕ 2 [1, 2]