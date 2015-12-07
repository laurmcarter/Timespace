
module Timespace

%default total

{-

'time' is a property of individual type variables.
A time interpreter should take a valuation of the set of variables in a type
to a new valuation of the same set, ie. a function from each type variable
to the number of steps required to observe an element of that type in the
larger structure.

'space', on the other hand, is a property of the larger structure, not of substructures.
A space interpreter should take an expression representing the space required to store
the input structure to an expression representing the space required for the output structure.
The valuation for the space required for each variable remains constant.

-}

data T
  = Zero
  | One
  | Add T T
  | Mul T T

syntax [a] "+" [b] = Add a b
syntax [a] "*" [b] = Mul a b

data Iso : T -> T -> Type where
  Id       : Iso a a
  Sym      : Iso a b -> Iso b a
  Trans    : Iso a b -> Iso b c -> Iso a c
  ----
  Add0L    : Iso (a + Zero) a
  Add0R    : Iso (Zero + a) a
  AddComm  : Iso (a + b) (b + a)
  AddAssoc : Iso ((a + b) + c) (a + (b + c))
  ----
  Mul1L    : Iso (a * One) a
  Mul1R    : Iso (One * a) a
  MulComm  : Iso (a * b) (b * a)
  MulAssoc : Iso ((a * b) * c) (a * (b * c))
  ----
  Annih    : Iso (a * Zero) Zero
  Distrib  : Iso (a * (b + c)) ((a * b) + (a * c))

obj : T -> Type
obj Zero      = Void
obj One       = Unit
obj (Add x y) = Either (obj x) (obj y)
obj (Mul x y) = Pair   (obj x) (obj y)

time : T -> Nat
time Zero      = 0
time One       = 1
time (Add a b) = max (time a) (time b) + 1
time (Mul a b) = max (time a) (time b)

space : T -> Nat
space Zero      = 0
space One       = 1
space (Add x y) = max (space x) (space y)
space (Mul x y) = space x + space y

record Bijection (a : T) (b : T) (f : T -> Type) (fwd : f a -> f b) (bwd : f b -> f a) where
  constructor MkBij
  fwd_bwd : (x : f a) -> bwd (fwd x) = x
  bwd_fwd : (x : f b) -> fwd (bwd x) = x

{-
record Bijection (a : T) (b : T) (f : obj a -> obj b) (g : obj b -> obj a) where
  constructor MkBij
  fwd_bwd : (o : p a) -> g (f o) = o
  bwd_fwd : (o : p b) -> f (g o) = o
  -}

mutual
  interpFwd : Iso a b -> obj a -> obj b
  interpFwd Id          x = x
  interpFwd (Sym i)     x = interpBwd i x
  interpFwd (Trans i j) x = interpFwd j (interpFwd i x)
  interpFwd Add0L       x = case x of
                            Left  a => a
                            Right b => void b
  interpFwd Add0R       x = case x of
                            Left  a => void a
                            Right b => b
  interpFwd AddComm     x = case x of
                            Left  a => Right a
                            Right b => Left  b
  interpFwd AddAssoc    x = case x of
                            Left (Left  a) => Left a
                            Left (Right b) => Right (Left b)
                            Right c        => Right (Right c)
  interpFwd Mul1L       x = case x of
                            (x,()) => x
  interpFwd Mul1R       x = case x of
                            ((),x) => x
  interpFwd MulComm     x = case x of
                            (a,b) => (b,a)
  interpFwd MulAssoc    x = case x of
                            ((a,b),c) => (a,(b,c))
  interpFwd Annih       x = case x of
                            (_,b) => b
  interpFwd Distrib     x = case x of
                            (a,bc) => case bc of
                              Left  b => Left  (a,b)
                              Right c => Right (a,c)
  
  interpBwd : Iso a b -> obj b -> obj a
  interpBwd Id          x = x
  interpBwd (Sym i)     x = interpFwd i x
  interpBwd (Trans i j) x = interpBwd i (interpBwd j x)
  interpBwd Add0L       x = Left x
  interpBwd Add0R       x = Right x
  interpBwd AddComm     x = case x of
                             Left  a => Right a
                             Right b => Left  b
  interpBwd AddAssoc    x = case x of
                             Left a          => Left (Left  a)
                             Right (Left  b) => Left (Right b)
                             Right (Right c) => Right c
  interpBwd Mul1L       x = (x,())
  interpBwd Mul1R       x = ((),x)
  interpBwd MulComm     x = case x of
                             (a,b) => (b,a)
  interpBwd MulAssoc    x = case x of
                             (a,(b,c)) => ((a,b),c)
  interpBwd Annih       x = void x
  interpBwd Distrib     x = case x of
                             Left  (a,b) => (a,Left  b)
                             Right (a,c) => (a,Right c)

interpBij : (i : Iso a b) -> Bijection a b obj (interpFwd i) (interpBwd i)
interpBij i = ?interpBij_rhs

{-

interpBij Id          = MkBij (\_ => Refl) (\_ => Refl)
interpBij (Sym j) with (interpBij j)
  | MkBij fb bf       = MkBij bf fb
interpBij (Trans j k) with (interpBij j)
  | MkBij fbj bfj with (interpBij k)
    | MkBij fbk bfk   = MkBij (\x => replace {P = \o => interpBwd j o = x} (sym (fbk (interpFwd  j x))) (fbj x))
                              (\x => replace {P = \o => interpFwd  k o = x} (sym (bfj (interpBwd k x))) (bfk x))
interpBij Add0L       = MkBij (\x => case x of
                                Left  _ => Refl
                                Right b => void b
                              )
                              (\_ => Refl)
interpBij Add0R       = MkBij (\x => case x of
                                Left  a => void a
                                Right _ => Refl
                              )
                              (\_ => Refl)
interpBij AddComm     = MkBij (\x => case x of
                                Left  _ => Refl
                                Right _ => Refl
                              )
                              (\x => case x of
                                Left  _ => Refl
                                Right _ => Refl
                              )
interpBij AddAssoc    = MkBij (\x => case x of
                                Left (Left  _) => Refl
                                Left (Right _) => Refl
                                Right _        => Refl
                              )
                              (\x => case x of
                                Left _          => Refl
                                Right (Left  _) => Refl
                                Right (Right _) => Refl
                              )
interpBij Mul1L       = MkBij (\x => case x of
                                (_,()) => Refl
                              )
                              (\_ => Refl)
interpBij Mul1R       = MkBij (\x => case x of
                                ((),_) => Refl
                              )
                              (\_ => Refl)
interpBij MulComm     = MkBij (\x => case x of
                                (_,_) => Refl
                              )
                              (\x => case x of
                                (_,_) => Refl
                              )
interpBij MulAssoc    = MkBij (\x => case x of
                                ((_,_),_) => Refl
                              )
                              (\x => case x of
                                (_,(_,_)) => Refl
                              )
interpBij Annih       = MkBij (\x => case x of
                                (_,v) => void v
                              )
                              (\x => void x)
interpBij Distrib     = MkBij (\x => case x of
                                (_,bc) => case bc of
                                  Left  _ => Refl
                                  Right _ => Refl
                              )
                              (\x => case x of
                                Left  ab => case ab of
                                  (_,_) => Refl
                                Right ac => case ac of
                                  (_,_) => Refl
                              )
                              -}

{-
mutual
  clockFwd : Iso a b -> obj a -> Clock a -> (obj b, Clock b)
  clockFwd Id          n = n
  clockFwd (Sym i)     n = clockBwd i n
  clockFwd (Trans i j) n = clockFwd j (clockFwd i n)
  clockFwd Add0L       n = ?clockFwd_rhs_4
  clockFwd Add0R       n = ?clockFwd_rhs_5
  clockFwd AddComm     n = ?clockFwd_rhs_6
  clockFwd AddAssoc    n = ?clockFwd_rhs_7
  clockFwd Mul1L       n = ?clockFwd_rhs_8
  clockFwd Mul1R       n = ?clockFwd_rhs_9
  clockFwd MulComm     n = ?clockFwd_rhs_10
  clockFwd MulAssoc    n = ?clockFwd_rhs_11
  clockFwd Annih       n = ?clockFwd_rhs_12
  clockFwd Distrib     n = ?clockFwd_rhs_13
----
  clockBwd : Iso a b -> obj b -> Clock b -> (obj a, Clock a)
  clockBwd Id          n = n
  clockBwd (Sym i)     n = clockFwd i n
  clockBwd (Trans i j) n = clockBwd i (clockBwd j n)
  clockBwd Add0L       n = ?clockBwd_rhs_4
  clockBwd Add0R       n = ?clockBwd_rhs_5
  clockBwd AddComm     n = ?clockBwd_rhs_6
  clockBwd AddAssoc    n = ?clockBwd_rhs_7
  clockBwd Mul1L       n = ?clockBwd_rhs_8
  clockBwd Mul1R       n = ?clockBwd_rhs_9
  clockBwd MulComm     n = ?clockBwd_rhs_10
  clockBwd MulAssoc    n = ?clockBwd_rhs_11
  clockBwd Annih       n = ?clockBwd_rhs_12
  clockBwd Distrib     n = ?clockBwd_rhs_13
  -}

