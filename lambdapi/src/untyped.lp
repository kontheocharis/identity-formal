
constant symbol TmC : TYPE;

symbol lam : (TmC → TmC) → TmC;
symbol app : TmC → TmC → TmC;

// Function eta
rule lam (λ x , app $f.[] x) ↪ $f;

// Nat
symbol zero : TmC;
symbol succ : TmC → TmC;
symbol rec : TmC → (TmC → TmC) → TmC → TmC;
rule rec zero (λ x , succ x) $t ↪ $t;

// Bool
symbol true : TmC;
symbol false : TmC;

// Addition
symbol add : TmC → TmC → TmC;
rule add zero $b ↪ $b;
rule rec $a (λ x , succ x) $b ↪ add $a $b;

// Multiplication
symbol mul : TmC → TmC → TmC;
rule mul zero _ ↪ zero;
rule rec zero (λ x , add x $b.[]) $a ↪ mul $a $b;

// Recognising identity
assert ⊢ lam (λ x , rec zero (λ x , succ x) x) ≡ lam (λ x , x);
assertnot ⊢ lam (λ x , rec zero (λ x , zero) x) ≡ lam (λ x , x);

// Recognising addition
assert ⊢ lam (λ x , lam (λ y , rec y (λ z , succ z) x)) ≡ lam (λ x , lam (λ y , add y x));

// Binary recursor
symbol rec2 : Π (zz : TmC) (zs : TmC) (sz : TmC) (ss : TmC → TmC) , TmC → TmC → TmC;

// Nat equality
symbol nat-eq : TmC → TmC → TmC;
// Can add constant-folding equations
rule rec2 true false false (λ x , x) $a $b ↪ nat-eq $a $b;

// // Case analysis
// symbol fix : (TmC → TmC) → TmC;
// symbol case : Π (z : TmC) (s : TmC → TmC) , TmC → TmC;
// rule fix (λ f , lam (λ a , lam (λ b , case (case true (λ _ , false) $b.[]) (λ x , case false (λ y , app (app f x) y) $b.[]) $a.[]))) ↪ nat-eq $a $b;