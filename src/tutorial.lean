#check "hello world!"
#check (27 + 9) * 33
#check [(1, 2), (3, 4), (5, 6)] ++ [(7, 8), (9, 10)]
#eval [(1, 2), (3, 4), (5, 6)] ++ [(7, 8), (9, 10)]

def double (n : ℕ) : ℕ := n + n
#check double
 

section
  variables (G : Type) [group G]
  variables g₁ g₂ : G

  #check g₂⁻¹ * g₁ * g₂

end

def even (n : ℕ) : Prop := ∃ m, n = 2 * m
example : even 10 := 
begin
 rw [even],
 existsi 5,
 refl
end
--(|5, rfl|)       --proof 10 is even