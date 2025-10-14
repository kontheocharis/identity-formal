
constant symbol TmC : TYPE;

symbol lam : (TmC → TmC) → TmC;
symbol app : TmC → TmC → TmC;
symbol error : TmC;

// Function eta
// rule lam (λ x , app $f.[] x) ↪ $f;

// Nat
symbol zero : TmC;
symbol succ : TmC → TmC;
symbol rec : TmC → (TmC → TmC → TmC) → TmC → TmC;
rule rec zero (λ x x' , succ x) $t ↪ $t;
// rule rec $z $s zero ↪ $z;
// rule rec $z $s (succ $n) ↪ $s $n (rec $z $s $n);

// Bool
symbol true : TmC;
symbol false : TmC;

// Addition
symbol add : TmC → TmC → TmC;
rule add zero $b ↪ $b;
rule rec $b (λ x x' , succ x') $a ↪ add $a $b;

// Predecessor
symbol pred : TmC → TmC;
rule rec error (λ x x' , x) $n ↪ pred $n;

// Subtraction
symbol sub : TmC → TmC → TmC;
rule rec $a (λ x x' , pred x') $b ↪ sub $a $b;

// Multiplication
symbol mul : TmC → TmC → TmC;
rule mul zero _ ↪ zero;
rule rec zero (λ x x' , add x $b.[]) $a ↪ mul $a $b;

// Recognising identity
assert ⊢ lam (λ x , rec zero (λ x x' , succ x) x) ≡ lam (λ x , x);
assertnot ⊢ lam (λ x , rec zero (λ x x' , zero) x) ≡ lam (λ x , x);

// Recognising addition
assert ⊢ lam (λ x , lam (λ y , rec y (λ z z' , succ z') x)) ≡ lam (λ x , lam (λ y , add x y));


// Binary recursor
symbol rec2 : Π (zz : TmC) (zs : TmC) (sz : TmC) (ss : TmC → TmC) , TmC → TmC → TmC;

// Nat equality
symbol nat-eq : TmC → TmC → TmC;
// Can add constant-folding equations
rule rec2 true false false (λ x , x) $a $b ↪ nat-eq $a $b;

// n - k - 1 test
compute lam (λ n , lam (λ k ,
          rec // match on x
            error // if x = 0 then error
            (λ n' n'r ,
              rec // if x = z + 1 then match on y
                n' // if y = 0 then return z
                (λ k' k'r , rec zero (λ n'' n''r , n'') n') // if y = w + 1 then return ??
                k
            )
            n
          ));
          