require open src.untyped;

constant symbol Ty : TYPE;
constant symbol TmL : Ty → TYPE;
constant symbol TmE : Π [A] , TmL A → TmC → TYPE;

// Normal functions

constant symbol Pi : Π (A : Ty) , (TmL A → Ty) → Ty;

symbol lamL : Π [A] [B] , (Π (x : TmL A) , TmL (B x)) → TmL (Pi A B);
symbol appL : Π [A] [B] , TmL (Pi A B) → Π (x : TmL A) , TmL (B x);

symbol lamE : Π [A] [B]
  [fL : (Π (x : TmL A) , TmL (B x))]
  [fC : TmC → TmC],
  (Π [xL] [xC] (x : TmE xL xC) , TmE (fL xL) (fC xC)) → TmE (lamL fL) (lam fC);
symbol appE : Π [A] [B]
  [fL : TmL (Pi A B)]
  [fC : TmC]
  [xL : TmL A]
  [xC : TmC],
  TmE fL fC → TmE xL xC → TmE (appL [A] [B] fL xL) (app fC xC);

// Identity functions

constant symbol PiID : Π (A : Ty) , (TmL A → Ty) → Ty;

symbol lamLID : Π [A] [B] , (Π (x : TmL A) , TmL (B x)) → TmL (PiID A B);
symbol appLID : Π [A] [B] , TmL (PiID A B) → Π (x : TmL A) , TmL (B x);

symbol lamEID : Π [A] [B]
  [fL : (Π (x : TmL A) , TmL (B x))] ,
  (Π [xL] [xC] (x : TmE xL xC) , TmE (fL xL) xC) → TmE (lamLID fL) (lam (λ x , x));
symbol appEID : Π [A] [B]
  [fL : TmL (PiID A B)]
  [fC : TmC]
  [xL : TmL A]
  [xC : TmC],
  TmE fL fC → TmE xL xC → TmE (appLID [A] [B] fL xL) xC;

// Nat

constant symbol Nat : Ty;

symbol zeroL : TmL Nat;
symbol succL : TmL Nat → TmL Nat;
symbol recL : Π [A] , TmL A → (TmL A → TmL A) → TmL Nat → TmL A;

symbol zeroE : TmE zeroL zero;
symbol succE : Π [nL] [nC] (n : TmE nL nC) , TmE (succL nL) (succ nC);
symbol recE : Π [A] [zL] [zC] [sL] [sC] [nL] [nC]
  (z : TmE zL zC)
  (s : Π [xL] [xC] (x : TmE xL xC) , TmE (sL xL) (sC xC)) ,
  TmE nL nC → TmE (recL [A] zL sL nL) (rec zC sC nC);
    
// Fin

constant symbol Fin : TmL Nat → Ty;

symbol fzeroL : Π [n] , TmL (Fin (succL n));
symbol fsuccL : Π [n] , TmL (Fin n) → TmL (Fin (succL n));
symbol frecL : Π [A]
  (z : Π [n] , TmL (A (succL n)))
  (s : Π [n] , TmL (A n) → TmL (A (succL n))) ,
  Π [n] , TmL (Fin n) → TmL (A n);
  
symbol fzeroE : Π [nL] , TmE (fzeroL [nL]) zero;
symbol fsuccE : Π [nL] [fL] [fC] (f : TmE fL fC) , TmE (fsuccL [nL] fL) (succ fC);
symbol frecE : Π [A] [zL] [zC] [sL] [sC]
  (z : Π [nL] , TmE (zL nL) zC)
  (s : Π [nL] [fL] [fC] (f : TmE fL fC) , TmE (sL nL fL) (sC fC)) ,
  Π [nL] [fL : TmL (Fin nL)] [fC] (f : TmE fL fC) , TmE (frecL [A] zL sL fL) (rec zC sC fC);

// Recognising identities

// Actual identity is identity:
assert ⊢ lamE (λ _ _ x , x) : _;
assert ⊢ lamEID (λ _ _ x , x) : _;

// Nat identity is identity:
assert ⊢ lamE (λ _ _ x , recE zeroE (λ _ _ x , succE x) x) : _;
assert ⊢ lamE (λ _ _ x , recE zeroE (λ _ _ x , zeroE) x) : _;

// Always zero is not identity:
assert ⊢ lamE (λ _ _ x , recE zeroE (λ _ _ x , zeroE) x) : _;
assertnot ⊢ lamEID (λ _ _ x , recE zeroE (λ _ _ x , zeroE) x) : _;

// Fin to nat is identity:
assert ⊢ lamEID (λ _ _ x , frecE (λ _ , zeroE) (λ _ _ _ x , succE x) x) : _;

// Identity-guarded of above is still identity:
assert ⊢ lamE [PiID Nat (λ _ , Nat)] (λ _ _ f ,
  lamEID (λ _ _ x ,
    frecE
      (λ _ , appEID f zeroE)
      (λ _ _ _ x , appEID f (succE (appEID f x)))
      x
    )) : _;

// It typechecks if `f` is a normal function and the result is not identity:
assert ⊢ lamE [Pi Nat (λ _ , Nat)] (λ _ _ f ,
  lamE (λ _ _ x , frecE (λ _ , appE f zeroE) (λ _ _ _ x , succE x) x)) : _;

// It does not typecheck if `f` is a normal function and the result is identity:
assertnot ⊢ lamE [Pi Nat (λ _ , Nat)] (λ _ _ f ,
  lamEID (λ _ _ x , frecE (λ _ , appE f zeroE) (λ _ _ _ x , succE x) x)) : _;
  
// Nat addition is addition:
assert ⊢ lamE (λ _ _ x , lamE (λ _ _ y , recE y (λ _ _ z , succE z) x))
  : TmE _ (lam (λ x, lam (λ y, add y x)));

// Nat addition is not identity:
assertnot ⊢ lamE (λ _ _ x , lamEID (λ _ _ y , recE y (λ _ _ z , succE z) x)) : _;