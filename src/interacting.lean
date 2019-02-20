section i1
    variables x y : ℕ
    def double := x + x

    theorem t1 : double (x + y) = double x + double y :=
        by simp [double]

    theorem t2 : double (x * y) = double x * y :=
    begin
        simp [double],
        rw add_mul,
    end
end i1

section
    variables (x y z : ℕ)
    variables (h1 : x = y) (h2 : y = z)
    include h1 h2
    theorem foo : x = z :=
    begin
        --rw [h1, h2]
        transitivity y,
        repeat {assumption}
    end
    
    omit h1 h2
    theorem bar : x = z :=
    eq.trans h1 h2
    
    theorem baz : x = x := 
    begin
        reflexivity 
    end
end

--instace ?
--attribute ?
