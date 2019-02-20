/- there are three steps involved:
1 - declare a family of inductive types to be a type class.
2 - declare instances of the type class.
3 - mark some implicit arguments with square brackets instead of curly brackets, to inform 
    the elaborator that these arguments should be inferred by the type class mechanism.-/

/- The standard library defines a type class inhabited : Type -> Type to enable type class 
inference to infer a “default” or “arbitrary” element of an inhabited type.  -/

--1
class inhabited' (α : Type _) :=
    (default' : α) 
--2
instance Prop_inhabited : inhabited' Prop :=
    ⟨true⟩ --inhabited'.mk true  
instance bool_inhabited : inhabited' bool :=
    ⟨tt⟩ --inhabited'.mk tt
instance nat_inhabited : inhabited' nat :=
    ⟨0⟩ --inhabited'.mk 0
instance unit_inhabited : inhabited' unit :=
    ⟨()⟩ --inhabited'.mk ()       

/- Whenever the elaborator is looking for a value to assign to an
argument ?M of type inhabited α for some α, it can check the list for a suitable instance. -/
--3
def default' (α : Type)[s:inhabited' α] : α :=
    @inhabited'.default' α s


#check default' Prop -- Prop
#check default' nat -- N
#reduce default Prop -- true
#reduce default nat -- 0

/- Sometimes we want to think of the default element of a type as being an arbitrary element, 
whose specific value should not play a role in our proofs. For that purpose, we can write 
arbitrary α instead of default α.  -/

----------------CHAINING INSTANCES--------------------------------------???
--the following definition shows that if two types α and β are inhabited, then so is their product:
instance prod_inhabited {α β : Type} [inhabited' α] [inhabited' β] : inhabited' (prod α β) :=
    ⟨(default' α, default' β)⟩
    
#check default (nat × bool)
#reduce default (nat × bool)    

instance inhabited_fun (α : Type) {β : Type} [inhabited β] : inhabited (α -> β) :=
    ⟨(λ a : α, default β)⟩
#check default (nat -> nat × bool)
#reduce default (nat -> nat × bool)

---------------INFERING NOTATION----------------------------------------
universes u
class has_add' (α : Type u) :=
(add' : α -> α -> α)
def add' {α : Type u} [has_add' α] : α -> α -> α := has_add'.add'
notation a ` + ` b := add' a b  --refers to the addition that is appropriate 
                                --to the type of a and b

/- The add function is designed to find an instance of has_add α for the given type, α, and apply the
corresponding binary addition function. -/
instance nat_has_add : has_add' nat :=
    ⟨nat.add⟩
instance bool_has_add : has_add' bool :=
    ⟨bor⟩
#check 4 + 5 --????????????????????????????
#check tt + ff -- bool

---------------DECIDABLE PROPOSITIONS------------------------------
---ite dite ????????????????????????????????????

open nat
def step' (a b x : ℕ) : ℕ :=
    if x < a ∨ x > b then 0 else 1

set_option pp.implicit true             --?set_option??????????????????????
#reduce step' 2 1 5

/- dec_trivial will succeed any time the inferred decision procedure for c has enough 
information to evaluate, definitionally, to the is_true case. -/
example : 0 = 0 ∧ (5 < 2 ∨ 3 < 7) := dec_trivial

---------MANAGING TYPE CLASS INFERENCE------------------------------
#print classes
#print instances inhabited

/- Lean allows us to declare three kinds of coercions:
1 - from a family of types to another family of types
2 - from a family of types to the class of sorts
    "view any element of a member of the source family as a type"
3 - from a family of types to the class of function types 
    "view any element of the source family as a function" -/

--1 
--define a coercion from bool to Prop    
instance bool_to_Prop : has_coe bool Prop :=
    ⟨λ b, b = tt⟩

#reduce if tt then 3 else 5
#reduce if ff then 3 else 5

variables n m : nat
variable i : int
#check coe n + i --with no coe we have error


--2
--allows us to view the elements of F a1 ... an as types

/- a semigroup consists of a type, carrier, and a multiplication, mul, with the property that
the multiplication is associative. -/
structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier -> carrier -> carrier)
    (mul_assoc : ∀ a b c : carrier,
    mul (mul a b) c = mul a (mul b c))

--The instance command allows us to write a * b instead of Semigroup
instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩