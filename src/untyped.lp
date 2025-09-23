
constant symbol TmC : TYPE;

symbol lam : (TmC → TmC) → TmC;
symbol app : TmC → TmC → TmC;

symbol zero : TmC;
symbol succ : TmC → TmC;

// Function eta
rule lam (λ x , app $f.[] x) ↪ $f;

// Recursor
symbol rec : TmC → (TmC → TmC) → TmC → TmC;
rule rec zero (λ x , succ x) $t ↪ $t;

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

// Recognising addition
assert ⊢ lam (λ x , lam (λ y , rec y (λ z , succ z) x)) ≡ lam (λ x , lam (λ y , add y x));