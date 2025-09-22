
constant symbol Tm : TYPE;

symbol lam : (Tm → Tm) → Tm;
symbol app : Tm → Tm → Tm;

symbol zero : Tm;
symbol succ : Tm → Tm;

// Function eta
rule lam (λ x , app $f.[] x) ↪ $f;

// Recursor
symbol rec : Tm → (Tm → Tm) → Tm → Tm;
rule rec zero (λ x , succ x) $t ↪ $t;

// Addition
symbol add : Tm → Tm → Tm;
rule add zero $b ↪ $b;
rule rec $a (λ x , succ x) $b ↪ add $a $b;

// Multiplication
symbol mul : Tm → Tm → Tm;
rule rec zero (λ x , add x $b.[]) $a ↪ mul $a $b;
