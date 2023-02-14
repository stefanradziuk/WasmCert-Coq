{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Progress_extracted where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
-- NOTE: added import manually
import qualified GHC.Exts
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
-- NOTE: changed manually from Base to Exts
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec =
  and_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

type Empty_set = () -- empty inductive

empty_set_rect :: Empty_set -> a1
empty_set_rect _ =
  Prelude.error "absurd case"

empty_set_rec :: Empty_set -> a1
empty_set_rec =
  empty_set_rect

data Unit =
   Tt

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

xorb :: Bool -> Bool -> Bool
xorb b1 b2 =
  case b1 of {
   True -> case b2 of {
            True -> False;
            False -> True};
   False -> b2}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

data Option a =
   Some a
 | None

option_map :: (a1 -> a2) -> (Option a1) -> Option a2
option_map f o =
  case o of {
   Some a -> Some (f a);
   None -> None}

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub k l}}

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False -> case b2 of {
             True -> False;
             False -> True}}

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Bool -> Reflect
iff_reflect b =
  case b of {
   True -> and_rec (\_ _ -> ReflectT);
   False -> and_rec (\_ _ -> ReflectF)}

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

apply :: (a1 -> a2) -> a2 -> (Option a1) -> a2
apply f x u =
  case u of {
   Some y -> f y;
   None -> x}

bind :: (a1 -> Option a2) -> (Option a1) -> Option a2
bind f =
  apply f None

type Simpl_fun aT rT =
  aT -> rT
  -- singleton inductive, whose constructor was SimplFun
  
fun_of_simpl :: (Simpl_fun a1 a2) -> a1 -> a2
fun_of_simpl f =
  f

of_void :: Empty_set -> a1
of_void _ =
  Prelude.error "absurd case"

addb :: Bool -> Bool -> Bool
addb b =
  case b of {
   True -> negb;
   False -> (\x -> x)}

isSome :: (Option a1) -> Bool
isSome u =
  case u of {
   Some _ -> True;
   None -> False}

is_left :: Sumbool -> Bool
is_left u =
  case u of {
   Left -> True;
   Right -> False}

type Decidable = Sumbool

iffP :: Bool -> Reflect -> Reflect
iffP _ pb =
  let {_evar_0_ = \_ _ _ -> ReflectT} in
  let {_evar_0_0 = \_ _ _ -> ReflectF} in
  case pb of {
   ReflectT -> _evar_0_ __ __ __;
   ReflectF -> _evar_0_0 __ __ __}

decP :: Bool -> Reflect -> Decidable
decP b _ =
  let {_evar_0_ = \_ -> Left} in
  let {_evar_0_0 = \_ -> Right} in
  case b of {
   True -> _evar_0_ __;
   False -> _evar_0_0 __}

idP :: Bool -> Reflect
idP b1 =
  case b1 of {
   True -> ReflectT;
   False -> ReflectF}

andP :: Bool -> Bool -> Reflect
andP b1 b2 =
  case b1 of {
   True -> case b2 of {
            True -> ReflectT;
            False -> ReflectF};
   False -> ReflectF}

type Pred t = t -> Bool

type PredType t =
  Any -> Pred t
  -- singleton inductive, whose constructor was PredType
  
type Pred_sort t = Any

type Rel t = t -> Pred t

type Mem_pred t = Pred t
  -- singleton inductive, whose constructor was Mem
  
pred_of_mem :: (Mem_pred a1) -> Pred_sort a1
pred_of_mem mp =
  unsafeCoerce mp

in_mem :: a1 -> (Mem_pred a1) -> Bool
in_mem x mp =
  unsafeCoerce pred_of_mem mp x

mem :: (PredType a1) -> (Pred_sort a1) -> Mem_pred a1
mem pT =
  pT

predType :: (a2 -> Pred a1) -> PredType a1
predType x =
  unsafeCoerce x

type Axiom t = t -> t -> Reflect

data Mixin_of t =
   Mixin (Rel t) (Axiom t)

op :: (Mixin_of a1) -> Rel a1
op m =
  case m of {
   Mixin op0 _ -> op0}

type Type = Mixin_of Any
  -- singleton inductive, whose constructor was Pack
  
type Sort = Any

class0 :: Type -> Mixin_of Sort
class0 cT3 =
  cT3

eq_op :: Type -> Rel Sort
eq_op t =
  op (class0 t)

eqP :: Type -> Axiom Sort
eqP t =
  let {_evar_0_ = \_ a -> a} in case t of {
                                 Mixin x x0 -> _evar_0_ x x0}

unit_eqP :: Axiom Unit
unit_eqP _ _ =
  ReflectT

unit_eqMixin :: Mixin_of Unit
unit_eqMixin =
  Mixin (\_ _ -> True) unit_eqP

unit_eqType :: Type
unit_eqType =
  unsafeCoerce unit_eqMixin

eqb0 :: Bool -> Bool -> Bool
eqb0 b =
  addb (negb b)

eqbP :: Axiom Bool
eqbP __top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_0 ->
    let {_evar_0_ = ReflectT} in
    let {_evar_0_0 = ReflectF} in
    case __top_assumption_0 of {
     True -> _evar_0_;
     False -> _evar_0_0}}
  in
  let {
   _evar_0_0 = \__top_assumption_0 ->
    let {_evar_0_0 = ReflectF} in
    let {_evar_0_1 = ReflectT} in
    case __top_assumption_0 of {
     True -> _evar_0_0;
     False -> _evar_0_1}}
  in
  case __top_assumption_ of {
   True -> _evar_0_;
   False -> _evar_0_0}

bool_eqMixin :: Mixin_of Bool
bool_eqMixin =
  Mixin eqb0 eqbP

bool_eqType :: Type
bool_eqType =
  unsafeCoerce bool_eqMixin

type Comparable t = t -> t -> Decidable

eq_comparable :: Type -> Comparable Sort
eq_comparable t x y =
  decP (eq_op t x y) (eqP t x y)

inj_eqAxiom :: Type -> (a1 -> Sort) -> Axiom a1
inj_eqAxiom eT f x y =
  iffP (eq_op eT (f x) (f y)) (eqP eT (f x) (f y))

injEqMixin :: Type -> (a1 -> Sort) -> Mixin_of a1
injEqMixin eT f =
  Mixin (\x y -> eq_op eT (f x) (f y)) (inj_eqAxiom eT f)

pcanEqMixin :: Type -> (a1 -> Sort) -> (Sort -> Option a1) -> Mixin_of a1
pcanEqMixin eT f _ =
  injEqMixin eT f

void_eqMixin :: Mixin_of Empty_set
void_eqMixin =
  pcanEqMixin unit_eqType of_void (fun_of_simpl (\_ -> None))

void_eqType :: Type
void_eqType =
  unsafeCoerce void_eqMixin

pair_eq :: Type -> Type -> Rel (Prod Sort Sort)
pair_eq t1 t2 u v =
  andb (eq_op t1 (fst u) (fst v)) (eq_op t2 (snd u) (snd v))

pair_eqP :: Type -> Type -> Axiom (Prod Sort Sort)
pair_eqP t1 t2 __top_assumption_ =
  let {
   _evar_0_ = \x1 x2 __top_assumption_0 ->
    let {
     _evar_0_ = \y1 y2 ->
      iffP
        (andb (eq_op t1 (fst (Pair x1 x2)) (fst (Pair y1 y2)))
          (eq_op t2 (snd (Pair x1 x2)) (snd (Pair y1 y2))))
        (andP (eq_op t1 (fst (Pair x1 x2)) (fst (Pair y1 y2)))
          (eq_op t2 (snd (Pair x1 x2)) (snd (Pair y1 y2))))}
    in
    case __top_assumption_0 of {
     Pair x x0 -> _evar_0_ x x0}}
  in
  case __top_assumption_ of {
   Pair x x0 -> _evar_0_ x x0}

prod_eqMixin :: Type -> Type -> Mixin_of (Prod Sort Sort)
prod_eqMixin t1 t2 =
  Mixin (pair_eq t1 t2) (pair_eqP t1 t2)

prod_eqType :: Type -> Type -> Type
prod_eqType t1 t2 =
  unsafeCoerce prod_eqMixin t1 t2

opt_eq :: Type -> (Option Sort) -> (Option Sort) -> Bool
opt_eq t u v =
  apply (\x -> apply (eq_op t x) False v) (negb (isSome v)) u

opt_eqP :: Type -> Axiom (Option Sort)
opt_eqP t _top_assumption_ =
  let {
   _evar_0_ = \x __top_assumption_ ->
    let {_evar_0_ = \y -> iffP (eq_op t x y) (eqP t x y)} in
    let {_evar_0_0 = ReflectF} in
    case __top_assumption_ of {
     Some x0 -> _evar_0_ x0;
     None -> _evar_0_0}}
  in
  let {
   _evar_0_0 = \__top_assumption_ ->
    let {_evar_0_0 = \_ -> ReflectF} in
    let {_evar_0_1 = ReflectT} in
    case __top_assumption_ of {
     Some x -> _evar_0_0 x;
     None -> _evar_0_1}}
  in
  case _top_assumption_ of {
   Some x -> _evar_0_ x;
   None -> _evar_0_0}

option_eqMixin :: Type -> Mixin_of (Option Sort)
option_eqMixin t =
  Mixin (opt_eq t) (opt_eqP t)

option_eqType :: Type -> Type
option_eqType t =
  unsafeCoerce option_eqMixin t

data Positive =
   XI Positive
 | XO Positive
 | XH

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p1 -> f p1 (positive_rect f f0 f1 p1);
   XO p1 -> f0 p1 (positive_rect f f0 f1 p1);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Positive

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

z_rect :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rect f f0 f1 z =
  case z of {
   Z0 -> f;
   Zpos x -> f0 x;
   Zneg x -> f1 x}

z_rec :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rec =
  z_rect

eqb1 :: Positive -> Positive -> Bool
eqb1 p q =
  case p of {
   XI p1 -> case q of {
             XI q0 -> eqb1 p1 q0;
             _ -> False};
   XO p1 -> case q of {
             XO q0 -> eqb1 p1 q0;
             _ -> False};
   XH -> case q of {
          XH -> True;
          _ -> False}}

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add0 :: Positive -> Positive -> Positive
add0 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add0 p q);
     XO q -> XO (add0 p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

pred_N :: Positive -> N
pred_N x =
  case x of {
   XI p -> Npos (XO p);
   XO p -> Npos (pred_double p);
   XH -> N0}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH -> case y of {
          XH -> IsNul;
          _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub0 :: Positive -> Positive -> Positive
sub0 x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add0 y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter :: (a1 -> a1) -> a1 -> Positive -> a1
iter f x n =
  case n of {
   XI n' -> f (iter f (iter f x n') n');
   XO n' -> iter f (iter f x n') n';
   XH -> f x}

div2 :: Positive -> Positive
div2 p =
  case p of {
   XI p1 -> p1;
   XO p1 -> p1;
   XH -> XH}

div2_up :: Positive -> Positive
div2_up p =
  case p of {
   XI p1 -> succ p1;
   XO p1 -> p1;
   XH -> XH}

size :: Positive -> Positive
size p =
  case p of {
   XI p1 -> succ (size p1);
   XO p1 -> succ (size p1);
   XH -> XH}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

eqb2 :: Positive -> Positive -> Bool
eqb2 p q =
  case p of {
   XI p1 -> case q of {
             XI q0 -> eqb2 p1 q0;
             _ -> False};
   XO p1 -> case q of {
             XO q0 -> eqb2 p1 q0;
             _ -> False};
   XH -> case q of {
          XH -> True;
          _ -> False}}

leb :: Positive -> Positive -> Bool
leb x y =
  case compare x y of {
   Gt -> False;
   _ -> True}

sqrtrem_step :: (Positive -> Positive) -> (Positive -> Positive) -> (Prod
                Positive Mask) -> Prod Positive Mask
sqrtrem_step f g p =
  case p of {
   Pair s y ->
    case y of {
     IsPos r ->
      let {s' = XI (XO s)} in
      let {r' = g (f r)} in
      case leb s' r' of {
       True -> Pair (XI s) (sub_mask r' s');
       False -> Pair (XO s) (IsPos r')};
     _ -> Pair (XO s) (sub_mask (g (f XH)) (XO (XO XH)))}}

sqrtrem :: Positive -> Prod Positive Mask
sqrtrem p =
  case p of {
   XI p1 ->
    case p1 of {
     XI p2 -> sqrtrem_step (\x -> XI x) (\x -> XI x) (sqrtrem p2);
     XO p2 -> sqrtrem_step (\x -> XO x) (\x -> XI x) (sqrtrem p2);
     XH -> Pair XH (IsPos (XO XH))};
   XO p1 ->
    case p1 of {
     XI p2 -> sqrtrem_step (\x -> XI x) (\x -> XO x) (sqrtrem p2);
     XO p2 -> sqrtrem_step (\x -> XO x) (\x -> XO x) (sqrtrem p2);
     XH -> Pair XH (IsPos XH)};
   XH -> Pair XH IsNul}

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

lor :: Positive -> Positive -> Positive
lor p q =
  case p of {
   XI p1 ->
    case q of {
     XI q0 -> XI (lor p1 q0);
     XO q0 -> XI (lor p1 q0);
     XH -> p};
   XO p1 ->
    case q of {
     XI q0 -> XI (lor p1 q0);
     XO q0 -> XO (lor p1 q0);
     XH -> XI p1};
   XH -> case q of {
          XO q0 -> XI q0;
          _ -> q}}

land :: Positive -> Positive -> N
land p q =
  case p of {
   XI p1 ->
    case q of {
     XI q0 -> nsucc_double (land p1 q0);
     XO q0 -> ndouble (land p1 q0);
     XH -> Npos XH};
   XO p1 ->
    case q of {
     XI q0 -> ndouble (land p1 q0);
     XO q0 -> ndouble (land p1 q0);
     XH -> N0};
   XH -> case q of {
          XO _ -> N0;
          _ -> Npos XH}}

ldiff :: Positive -> Positive -> N
ldiff p q =
  case p of {
   XI p1 ->
    case q of {
     XI q0 -> ndouble (ldiff p1 q0);
     XO q0 -> nsucc_double (ldiff p1 q0);
     XH -> Npos (XO p1)};
   XO p1 ->
    case q of {
     XI q0 -> ndouble (ldiff p1 q0);
     XO q0 -> ndouble (ldiff p1 q0);
     XH -> Npos p};
   XH -> case q of {
          XO _ -> Npos XH;
          _ -> N0}}

lxor :: Positive -> Positive -> N
lxor p q =
  case p of {
   XI p1 ->
    case q of {
     XI q0 -> ndouble (lxor p1 q0);
     XO q0 -> nsucc_double (lxor p1 q0);
     XH -> Npos (XO p1)};
   XO p1 ->
    case q of {
     XI q0 -> nsucc_double (lxor p1 q0);
     XO q0 -> ndouble (lxor p1 q0);
     XH -> Npos (XI p1)};
   XH -> case q of {
          XI q0 -> Npos (XO q0);
          XO q0 -> Npos (XI q0);
          XH -> N0}}

testbit :: Positive -> N -> Bool
testbit p n =
  case p of {
   XI p1 -> case n of {
             N0 -> True;
             Npos n0 -> testbit p1 (pred_N n0)};
   XO p1 -> case n of {
             N0 -> False;
             Npos n0 -> testbit p1 (pred_N n0)};
   XH -> case n of {
          N0 -> True;
          Npos _ -> False}}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op0 p a =
  case p of {
   XI p1 -> op0 a (iter_op op0 p1 (op0 a a));
   XO p1 -> iter_op op0 p1 (op0 a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op add x (S O)

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ (of_succ_nat x)}

eq_dec :: Positive -> Positive -> Sumbool
eq_dec x y =
  positive_rec (\_ h x0 ->
    case x0 of {
     XI p1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h p1);
     _ -> Right}) (\_ h x0 ->
    case x0 of {
     XO p1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h p1);
     _ -> Right}) (\x0 -> case x0 of {
                           XH -> Left;
                           _ -> Right}) x y

add1 :: N -> N -> N
add1 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (add0 p q)}}

succ_double :: N -> N
succ_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

double :: N -> N
double n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

succ_pos :: N -> Positive
succ_pos n =
  case n of {
   N0 -> XH;
   Npos p -> succ p}

add2 :: N -> N -> N
add2 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (add0 p q)}}

sub1 :: N -> N -> N
sub1 n m =
  case n of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n;
     Npos m' -> case sub_mask n' m' of {
                 IsPos p -> Npos p;
                 _ -> N0}}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> Npos (mul p q)}}

compare0 :: N -> N -> Comparison
compare0 n m =
  case n of {
   N0 -> case m of {
          N0 -> Eq;
          Npos _ -> Lt};
   Npos n' -> case m of {
               N0 -> Gt;
               Npos m' -> compare n' m'}}

eqb3 :: N -> N -> Bool
eqb3 n m =
  case n of {
   N0 -> case m of {
          N0 -> True;
          Npos _ -> False};
   Npos p -> case m of {
              N0 -> False;
              Npos q -> eqb2 p q}}

leb0 :: N -> N -> Bool
leb0 x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb :: N -> N -> Bool
ltb x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

pos_div_eucl :: Positive -> N -> Prod N N
pos_div_eucl a b =
  case a of {
   XI a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub1 r' b);
       False -> Pair (double q) r'}};
   XO a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub1 r' b);
       False -> Pair (double q) r'}};
   XH ->
    case b of {
     N0 -> Pair N0 (Npos XH);
     Npos p -> case p of {
                XH -> Pair (Npos XH) N0;
                _ -> Pair N0 (Npos XH)}}}

div_eucl :: N -> N -> Prod N N
div_eucl a b =
  case a of {
   N0 -> Pair N0 N0;
   Npos na -> case b of {
               N0 -> Pair N0 a;
               Npos _ -> pos_div_eucl na b}}

div :: N -> N -> N
div a b =
  fst (div_eucl a b)

lor0 :: N -> N -> N
lor0 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> ldiff p q}}

lxor0 :: N -> N -> N
lxor0 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> lxor p q}}

testbit0 :: N -> N -> Bool
testbit0 a n =
  case a of {
   N0 -> False;
   Npos p -> testbit p n}

to_nat0 :: N -> Nat
to_nat0 a =
  case a of {
   N0 -> O;
   Npos p -> to_nat p}

of_nat :: Nat -> N
of_nat n =
  case n of {
   O -> N0;
   S n' -> Npos (of_succ_nat n')}

nth_error :: (List a1) -> Nat -> Option a1
nth_error l n =
  case n of {
   O -> case l of {
         Nil -> None;
         Cons x _ -> Some x};
   S n0 -> case l of {
            Nil -> None;
            Cons _ l0 -> nth_error l0 n0}}

rev :: (List a1) -> List a1
rev l =
  case l of {
   Nil -> Nil;
   Cons x l' -> app (rev l') (Cons x Nil)}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (List a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   Nil -> a0;
   Cons b t -> fold_left f t (f a0 b)}

forallb :: (a1 -> Bool) -> (List a1) -> Bool
forallb f l =
  case l of {
   Nil -> True;
   Cons a l0 -> andb (f a) (forallb f l0)}

skipn :: Nat -> (List a1) -> List a1
skipn n l =
  case n of {
   O -> l;
   S n0 -> case l of {
            Nil -> Nil;
            Cons _ l0 -> skipn n0 l0}}

of_nat0 :: Nat -> Z
of_nat0 n =
  case n of {
   O -> Z0;
   S n0 -> Zpos (of_succ_nat n0)}

double0 :: Z -> Z
double0 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double0 :: Z -> Z
succ_double0 x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double0 (pos_sub p q);
     XO q -> succ_double0 (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double0 (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add3 :: Z -> Z -> Z
add3 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add0 x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add0 x' y')}}

opp :: Z -> Z
opp x =
  case x of {
   Z0 -> Z0;
   Zpos x0 -> Zneg x0;
   Zneg x0 -> Zpos x0}

pred :: Z -> Z
pred x =
  add3 x (Zneg XH)

sub2 :: Z -> Z -> Z
sub2 m n =
  add3 m (opp n)

mul1 :: Z -> Z -> Z
mul1 x y =
  case x of {
   Z0 -> Z0;
   Zpos x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zpos (mul x' y');
     Zneg y' -> Zneg (mul x' y')};
   Zneg x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zneg (mul x' y');
     Zneg y' -> Zpos (mul x' y')}}

pow_pos :: Z -> Positive -> Z
pow_pos z =
  iter (mul1 z) (Zpos XH)

pow :: Z -> Z -> Z
pow x y =
  case y of {
   Z0 -> Zpos XH;
   Zpos p -> pow_pos x p;
   Zneg _ -> Z0}

compare1 :: Z -> Z -> Comparison
compare1 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Eq;
          Zpos _ -> Lt;
          Zneg _ -> Gt};
   Zpos x' -> case y of {
               Zpos y' -> compare x' y';
               _ -> Gt};
   Zneg x' -> case y of {
               Zneg y' -> compOpp (compare x' y');
               _ -> Lt}}

leb1 :: Z -> Z -> Bool
leb1 x y =
  case compare1 x y of {
   Gt -> False;
   _ -> True}

ltb0 :: Z -> Z -> Bool
ltb0 x y =
  case compare1 x y of {
   Lt -> True;
   _ -> False}

geb :: Z -> Z -> Bool
geb x y =
  case compare1 x y of {
   Lt -> False;
   _ -> True}

gtb :: Z -> Z -> Bool
gtb x y =
  case compare1 x y of {
   Gt -> True;
   _ -> False}

max :: Z -> Z -> Z
max n m =
  case compare1 n m of {
   Lt -> m;
   _ -> n}

min :: Z -> Z -> Z
min n m =
  case compare1 n m of {
   Gt -> m;
   _ -> n}

to_nat1 :: Z -> Nat
to_nat1 z =
  case z of {
   Zpos p -> to_nat p;
   _ -> O}

to_N :: Z -> N
to_N z =
  case z of {
   Zpos p -> Npos p;
   _ -> N0}

of_nat1 :: Nat -> Z
of_nat1 n =
  case n of {
   O -> Z0;
   S n0 -> Zpos (of_succ_nat n0)}

of_N :: N -> Z
of_N n =
  case n of {
   N0 -> Z0;
   Npos p -> Zpos p}

to_pos :: Z -> Positive
to_pos z =
  case z of {
   Zpos p -> p;
   _ -> XH}

iter0 :: Z -> (a1 -> a1) -> a1 -> a1
iter0 n f x =
  case n of {
   Zpos p -> iter f x p;
   _ -> x}

pos_div_eucl0 :: Positive -> Z -> Prod Z Z
pos_div_eucl0 a b =
  case a of {
   XI a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = add3 (mul1 (Zpos (XO XH)) r) (Zpos XH)} in
      case ltb0 r' b of {
       True -> Pair (mul1 (Zpos (XO XH)) q) r';
       False -> Pair (add3 (mul1 (Zpos (XO XH)) q) (Zpos XH)) (sub2 r' b)}};
   XO a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = mul1 (Zpos (XO XH)) r} in
      case ltb0 r' b of {
       True -> Pair (mul1 (Zpos (XO XH)) q) r';
       False -> Pair (add3 (mul1 (Zpos (XO XH)) q) (Zpos XH)) (sub2 r' b)}};
   XH ->
    case leb1 (Zpos (XO XH)) b of {
     True -> Pair Z0 (Zpos XH);
     False -> Pair (Zpos XH) Z0}}

div_eucl0 :: Z -> Z -> Prod Z Z
div_eucl0 a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos _ -> pos_div_eucl0 a' b;
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add3 q (Zpos XH))) (add3 b r)}}};
   Zneg a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos _ ->
      case pos_div_eucl0 a' b of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add3 q (Zpos XH))) (sub2 b r)}};
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       Pair q r -> Pair q (opp r)}}}

div0 :: Z -> Z -> Z
div0 a b =
  case div_eucl0 a b of {
   Pair q _ -> q}

modulo :: Z -> Z -> Z
modulo a b =
  case div_eucl0 a b of {
   Pair _ r -> r}

quotrem :: Z -> Z -> Prod Z Z
quotrem a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a0 ->
    case b of {
     Z0 -> Pair Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (of_N r)};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (of_N r)}};
   Zneg a0 ->
    case b of {
     Z0 -> Pair Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (opp (of_N r))};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (opp (of_N r))}}}

quot :: Z -> Z -> Z
quot a b =
  fst (quotrem a b)

rem :: Z -> Z -> Z
rem a b =
  snd (quotrem a b)

even :: Z -> Bool
even z =
  case z of {
   Z0 -> True;
   Zpos p -> case p of {
              XO _ -> True;
              _ -> False};
   Zneg p -> case p of {
              XO _ -> True;
              _ -> False}}

odd :: Z -> Bool
odd z =
  case z of {
   Z0 -> False;
   Zpos p -> case p of {
              XO _ -> False;
              _ -> True};
   Zneg p -> case p of {
              XO _ -> False;
              _ -> True}}

div1 :: Z -> Z
div1 z =
  case z of {
   Z0 -> Z0;
   Zpos p -> case p of {
              XH -> Z0;
              _ -> Zpos (div2 p)};
   Zneg p -> Zneg (div2_up p)}

log2 :: Z -> Z
log2 z =
  case z of {
   Zpos p1 ->
    case p1 of {
     XI p -> Zpos (size p);
     XO p -> Zpos (size p);
     XH -> Z0};
   _ -> Z0}

sqrtrem0 :: Z -> Prod Z Z
sqrtrem0 n =
  case n of {
   Zpos p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair (Zpos s) (Zpos r);
       _ -> Pair (Zpos s) Z0}};
   _ -> Pair Z0 Z0}

testbit1 :: Z -> Z -> Bool
testbit1 a n =
  case n of {
   Z0 -> odd a;
   Zpos p ->
    case a of {
     Z0 -> False;
     Zpos a0 -> testbit a0 (Npos p);
     Zneg a0 -> negb (testbit0 (pred_N a0) (Npos p))};
   Zneg _ -> False}

shiftl :: Z -> Z -> Z
shiftl a n =
  case n of {
   Z0 -> a;
   Zpos p -> iter (mul1 (Zpos (XO XH))) a p;
   Zneg p -> iter div1 a p}

shiftr :: Z -> Z -> Z
shiftr a n =
  shiftl a (opp n)

lor1 :: Z -> Z -> Z
lor1 a b =
  case a of {
   Z0 -> b;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zpos (lor a0 b0);
     Zneg b0 -> Zneg (succ_pos (ldiff0 (pred_N b0) (Npos a0)))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (ldiff0 (pred_N a0) (Npos b0)));
     Zneg b0 -> Zneg (succ_pos (land0 (pred_N a0) (pred_N b0)))}}

land1 :: Z -> Z -> Z
land1 a b =
  case a of {
   Z0 -> Z0;
   Zpos a0 ->
    case b of {
     Z0 -> Z0;
     Zpos b0 -> of_N (land a0 b0);
     Zneg b0 -> of_N (ldiff0 (Npos a0) (pred_N b0))};
   Zneg a0 ->
    case b of {
     Z0 -> Z0;
     Zpos b0 -> of_N (ldiff0 (Npos b0) (pred_N a0));
     Zneg b0 -> Zneg (succ_pos (lor0 (pred_N a0) (pred_N b0)))}}

lxor1 :: Z -> Z -> Z
lxor1 a b =
  case a of {
   Z0 -> b;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> of_N (lxor a0 b0);
     Zneg b0 -> Zneg (succ_pos (lxor0 (Npos a0) (pred_N b0)))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (lxor0 (pred_N a0) (Npos b0)));
     Zneg b0 -> of_N (lxor0 (pred_N a0) (pred_N b0))}}

eq_dec0 :: Z -> Z -> Sumbool
eq_dec0 x y =
  z_rec (\x0 -> case x0 of {
                 Z0 -> Left;
                 _ -> Right}) (\p x0 ->
    case x0 of {
     Zpos p1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (eq_dec p p1);
     _ -> Right}) (\p x0 ->
    case x0 of {
     Zneg p1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (eq_dec p p1);
     _ -> Right}) x y

z_lt_dec :: Z -> Z -> Sumbool
z_lt_dec x y =
  case compare1 x y of {
   Lt -> Left;
   _ -> Right}

z_le_dec :: Z -> Z -> Sumbool
z_le_dec x y =
  case compare1 x y of {
   Gt -> Right;
   _ -> Left}

z_le_gt_dec :: Z -> Z -> Sumbool
z_le_gt_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_le_dec x y)

zeq_bool :: Z -> Z -> Bool
zeq_bool x y =
  case compare1 x y of {
   Eq -> True;
   _ -> False}

eqn :: Nat -> Nat -> Bool
eqn m n =
  case m of {
   O -> case n of {
         O -> True;
         S _ -> False};
   S m' -> case n of {
            O -> False;
            S n' -> eqn m' n'}}

eqnP :: Axiom Nat
eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

nat_eqMixin :: Mixin_of Nat
nat_eqMixin =
  Mixin eqn eqnP

nat_eqType :: Type
nat_eqType =
  unsafeCoerce nat_eqMixin

addn_rec :: Nat -> Nat -> Nat
addn_rec =
  add

addn :: Nat -> Nat -> Nat
addn =
  addn_rec

subn_rec :: Nat -> Nat -> Nat
subn_rec =
  sub

subn :: Nat -> Nat -> Nat
subn =
  subn_rec

leq :: Nat -> Nat -> Bool
leq m n =
  eq_op nat_eqType (unsafeCoerce subn m n) (unsafeCoerce O)

maxn :: Nat -> Nat -> Nat
maxn m n =
  case leq (S m) n of {
   True -> n;
   False -> m}

iter1 :: Nat -> (a1 -> a1) -> a1 -> a1
iter1 n f x =
  case n of {
   O -> x;
   S i -> f (iter1 i f x)}

nat_of_bool :: Bool -> Nat
nat_of_bool b =
  case b of {
   True -> S O;
   False -> O}

add4 :: Nat -> Nat -> Nat
add4 m n =
  case m of {
   O -> n;
   S m' -> add4 m' (S n)}

double1 :: Nat -> Nat
double1 n =
  case n of {
   O -> O;
   S n' -> add4 n' (S n)}

eq_binP :: Axiom N
eq_binP p q =
  iffP (eqb3 p q) (idP (eqb3 p q))

bin_nat_eqMixin :: Mixin_of N
bin_nat_eqMixin =
  Mixin eqb3 eq_binP

bin_nat_eqType :: Type
bin_nat_eqType =
  unsafeCoerce bin_nat_eqMixin

nat_of_pos :: Positive -> Nat
nat_of_pos p1 =
  case p1 of {
   XI p -> S (double1 (nat_of_pos p));
   XO p -> double1 (nat_of_pos p);
   XH -> S O}

nat_of_bin :: N -> Nat
nat_of_bin b =
  case b of {
   N0 -> O;
   Npos p -> nat_of_pos p}

size0 :: (List a1) -> Nat
size0 s =
  case s of {
   Nil -> O;
   Cons _ s' -> S (size0 s')}

ncons :: Nat -> a1 -> (List a1) -> List a1
ncons n x =
  iter1 n (\x0 -> Cons x x0)

cat :: (List a1) -> (List a1) -> List a1
cat s1 s2 =
  case s1 of {
   Nil -> s2;
   Cons x s1' -> Cons x (cat s1' s2)}

rcons :: (List a1) -> a1 -> List a1
rcons s z =
  case s of {
   Nil -> Cons z Nil;
   Cons x s' -> Cons x (rcons s' z)}

set_nth :: a1 -> (List a1) -> Nat -> a1 -> List a1
set_nth x0 s n y =
  case s of {
   Nil -> ncons n x0 (Cons y Nil);
   Cons x s' ->
    case n of {
     O -> Cons y s';
     S n' -> Cons x (set_nth x0 s' n' y)}}

find :: (Pred a1) -> (List a1) -> Nat
find a s =
  case s of {
   Nil -> O;
   Cons x s' -> case a x of {
                 True -> O;
                 False -> S (find a s')}}

filter :: (Pred a1) -> (List a1) -> List a1
filter a s =
  case s of {
   Nil -> Nil;
   Cons x s' ->
    case a x of {
     True -> Cons x (filter a s');
     False -> filter a s'}}

count :: (Pred a1) -> (List a1) -> Nat
count a s =
  case s of {
   Nil -> O;
   Cons x s' -> addn (nat_of_bool (a x)) (count a s')}

all :: (Pred a1) -> (List a1) -> Bool
all a s =
  case s of {
   Nil -> True;
   Cons x s' -> andb (a x) (all a s')}

drop :: Nat -> (List a1) -> List a1
drop n s =
  case s of {
   Nil -> s;
   Cons _ s' -> case n of {
                 O -> s;
                 S n' -> drop n' s'}}

take :: Nat -> (List a1) -> List a1
take n s =
  case s of {
   Nil -> Nil;
   Cons x s' -> case n of {
                 O -> Nil;
                 S n' -> Cons x (take n' s')}}

catrev :: (List a1) -> (List a1) -> List a1
catrev s1 s2 =
  case s1 of {
   Nil -> s2;
   Cons x s1' -> catrev s1' (Cons x s2)}

rev0 :: (List a1) -> List a1
rev0 s =
  catrev s Nil

eqseq :: Type -> (List Sort) -> (List Sort) -> Bool
eqseq t s1 s2 =
  case s1 of {
   Nil -> case s2 of {
           Nil -> True;
           Cons _ _ -> False};
   Cons x1 s1' ->
    case s2 of {
     Nil -> False;
     Cons x2 s2' -> andb (eq_op t x1 x2) (eqseq t s1' s2')}}

eqseqP :: Type -> Axiom (List Sort)
eqseqP t _top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_ ->
    let {_evar_0_ = ReflectT} in
    let {_evar_0_0 = \_ _ -> ReflectF} in
    case __top_assumption_ of {
     Nil -> _evar_0_;
     Cons x x0 -> _evar_0_0 x x0}}
  in
  let {
   _evar_0_0 = \x1 s1 iHs __top_assumption_ ->
    let {_evar_0_0 = ReflectF} in
    let {
     _evar_0_1 = \x2 s2 ->
      ssr_have (eqP t x1 x2) (\__top_assumption_0 ->
        let {
         _evar_0_1 = \_ ->
          let {_evar_0_1 = iffP (eqseq t s1 s2) (iHs s2)} in
          eq_rect x1 _evar_0_1 x2}
        in
        let {_evar_0_2 = \_ -> ReflectF} in
        case __top_assumption_0 of {
         ReflectT -> _evar_0_1 __;
         ReflectF -> _evar_0_2 __})}
    in
    case __top_assumption_ of {
     Nil -> _evar_0_0;
     Cons x x0 -> _evar_0_1 x x0}}
  in
  list_rect _evar_0_ _evar_0_0 _top_assumption_

seq_eqMixin :: Type -> Mixin_of (List Sort)
seq_eqMixin t =
  Mixin (eqseq t) (eqseqP t)

seq_eqType :: Type -> Type
seq_eqType t =
  unsafeCoerce seq_eqMixin t

mem_seq :: Type -> (List Sort) -> Sort -> Bool
mem_seq t s =
  case s of {
   Nil -> (\_ -> False);
   Cons y s' -> let {p = mem_seq t s'} in (\x -> orb (eq_op t x y) (p x))}

type Seq_eqclass = List Sort

pred_of_seq :: Type -> Seq_eqclass -> Pred_sort Sort
pred_of_seq t s =
  unsafeCoerce mem_seq t s

seq_predType :: Type -> PredType Sort
seq_predType t =
  predType (unsafeCoerce pred_of_seq t)

map0 :: (a1 -> a2) -> (List a1) -> List a2
map0 f s =
  case s of {
   Nil -> Nil;
   Cons x s' -> Cons (f x) (map0 f s')}

iota :: Nat -> Nat -> List Nat
iota m n =
  case n of {
   O -> Nil;
   S n' -> Cons m (iota (S m) n')}

solution_left :: a1 -> a2 -> a1 -> a2
solution_left =
  eq_rect_r

solution_right :: a1 -> a2 -> a1 -> a2
solution_right t x x0 =
  eq_rect_r x0 (\x1 -> x1) t x

shift_nat :: Nat -> Positive -> Positive
shift_nat n z =
  nat_rect z (\_ x -> XO x) n

shift_pos :: Positive -> Positive -> Positive
shift_pos n z =
  iter (\x -> XO x) z n

two_power_nat :: Nat -> Z
two_power_nat n =
  Zpos (shift_nat n XH)

two_power_pos :: Positive -> Z
two_power_pos x =
  Zpos (shift_pos x XH)

two_p :: Z -> Z
two_p x =
  case x of {
   Z0 -> Zpos XH;
   Zpos y -> two_power_pos y;
   Zneg _ -> Z0}

zeq :: Z -> Z -> Sumbool
zeq =
  eq_dec0

zlt :: Z -> Z -> Sumbool
zlt =
  z_lt_dec

zle :: Z -> Z -> Sumbool
zle =
  z_le_gt_dec

proj_sumbool :: Sumbool -> Bool
proj_sumbool a =
  case a of {
   Left -> True;
   Right -> False}

p_mod_two_p :: Positive -> Nat -> Z
p_mod_two_p p n =
  case n of {
   O -> Z0;
   S m ->
    case p of {
     XI q -> succ_double0 (p_mod_two_p q m);
     XO q -> double0 (p_mod_two_p q m);
     XH -> Zpos XH}}

zshiftin :: Bool -> Z -> Z
zshiftin b x =
  case b of {
   True -> succ_double0 x;
   False -> double0 x}

zzero_ext :: Z -> Z -> Z
zzero_ext n x =
  iter0 n (\rec x0 -> zshiftin (odd x0) (rec (div1 x0))) (\_ -> Z0) x

zsign_ext :: Z -> Z -> Z
zsign_ext n x =
  iter0 (pred n) (\rec x0 -> zshiftin (odd x0) (rec (div1 x0))) (\x0 ->
    case andb (odd x0) (proj_sumbool (zlt Z0 n)) of {
     True -> Zneg XH;
     False -> Z0}) x

z_one_bits :: Nat -> Z -> Z -> List Z
z_one_bits n x i =
  case n of {
   O -> Nil;
   S m ->
    case odd x of {
     True -> Cons i (z_one_bits m (div1 x) (add3 i (Zpos XH)));
     False -> z_one_bits m (div1 x) (add3 i (Zpos XH))}}

p_is_power2 :: Positive -> Bool
p_is_power2 p =
  case p of {
   XI _ -> False;
   XO q -> p_is_power2 q;
   XH -> True}

z_is_power2 :: Z -> Option Z
z_is_power2 x =
  case x of {
   Zpos p -> case p_is_power2 p of {
              True -> Some (log2 x);
              False -> None};
   _ -> None}

zsize :: Z -> Z
zsize x =
  case x of {
   Zpos p -> Zpos (size p);
   _ -> Z0}

digits2_pos :: Positive -> Positive
digits2_pos n =
  case n of {
   XI p -> succ (digits2_pos p);
   XO p -> succ (digits2_pos p);
   XH -> XH}

zdigits2 :: Z -> Z
zdigits2 n =
  case n of {
   Z0 -> n;
   Zpos p -> Zpos (digits2_pos p);
   Zneg p -> Zpos (digits2_pos p)}

iter_pos :: (a1 -> a1) -> Positive -> a1 -> a1
iter_pos f n x =
  case n of {
   XI n' -> iter_pos f n' (iter_pos f n' (f x));
   XO n' -> iter_pos f n' (iter_pos f n' x);
   XH -> f x}

data Location =
   Loc_Exact
 | Loc_Inexact Comparison

cond_Zopp :: Bool -> Z -> Z
cond_Zopp b m =
  case b of {
   True -> opp m;
   False -> m}

type Radix = Z
  -- singleton inductive, whose constructor was Build_radix
  
radix_val :: Radix -> Z
radix_val r =
  r

radix2 :: Radix
radix2 =
  Zpos (XO XH)

zpos_div_eucl_aux1 :: Positive -> Positive -> Prod Z Z
zpos_div_eucl_aux1 a b =
  case b of {
   XI _ -> pos_div_eucl0 a (Zpos b);
   XO b' ->
    case a of {
     XI a' ->
      case zpos_div_eucl_aux1 a' b' of {
       Pair q r -> Pair q (add3 (mul1 (Zpos (XO XH)) r) (Zpos XH))};
     XO a' ->
      case zpos_div_eucl_aux1 a' b' of {
       Pair q r -> Pair q (mul1 (Zpos (XO XH)) r)};
     XH -> Pair Z0 (Zpos a)};
   XH -> Pair (Zpos a) Z0}

zpos_div_eucl_aux :: Positive -> Positive -> Prod Z Z
zpos_div_eucl_aux a b =
  case compare a b of {
   Eq -> Pair (Zpos XH) Z0;
   Lt -> Pair Z0 (Zpos a);
   Gt -> zpos_div_eucl_aux1 a b}

zfast_div_eucl :: Z -> Z -> Prod Z Z
zfast_div_eucl a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a' ->
    case b of {
     Z0 -> Pair Z0 (case modulo (Zpos XH) Z0 of {
                     Z0 -> Z0;
                     _ -> a});
     Zpos b' -> zpos_div_eucl_aux a' b';
     Zneg b' ->
      case zpos_div_eucl_aux a' b' of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add3 q (Zpos XH))) (add3 b r)}}};
   Zneg a' ->
    case b of {
     Z0 -> Pair Z0 (case modulo (Zpos XH) Z0 of {
                     Z0 -> Z0;
                     _ -> a});
     Zpos b' ->
      case zpos_div_eucl_aux a' b' of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add3 q (Zpos XH))) (sub2 b r)}};
     Zneg b' -> case zpos_div_eucl_aux a' b' of {
                 Pair q r -> Pair q (opp r)}}}

iter_nat :: (a1 -> a1) -> Nat -> a1 -> a1
iter_nat f n x =
  case n of {
   O -> x;
   S n' -> iter_nat f n' (f x)}

fLT_exp :: Z -> Z -> Z -> Z
fLT_exp emin prec1 e =
  max (sub2 e prec1) emin

new_location_even :: Z -> Z -> Location -> Location
new_location_even nb_steps k l =
  case zeq_bool k Z0 of {
   True -> case l of {
            Loc_Exact -> l;
            Loc_Inexact _ -> Loc_Inexact Lt};
   False -> Loc_Inexact
    (case compare1 (mul1 (Zpos (XO XH)) k) nb_steps of {
      Eq -> case l of {
             Loc_Exact -> Eq;
             Loc_Inexact _ -> Gt};
      x -> x})}

new_location_odd :: Z -> Z -> Location -> Location
new_location_odd nb_steps k l =
  case zeq_bool k Z0 of {
   True -> case l of {
            Loc_Exact -> l;
            Loc_Inexact _ -> Loc_Inexact Lt};
   False -> Loc_Inexact
    (case compare1 (add3 (mul1 (Zpos (XO XH)) k) (Zpos XH)) nb_steps of {
      Eq -> case l of {
             Loc_Exact -> Lt;
             Loc_Inexact l0 -> l0};
      x -> x})}

new_location :: Z -> Z -> Location -> Location
new_location nb_steps =
  case even nb_steps of {
   True -> new_location_even nb_steps;
   False -> new_location_odd nb_steps}

cond_incr :: Bool -> Z -> Z
cond_incr b m =
  case b of {
   True -> add3 m (Zpos XH);
   False -> m}

round_sign_DN :: Bool -> Location -> Bool
round_sign_DN s l =
  case l of {
   Loc_Exact -> False;
   Loc_Inexact _ -> s}

round_sign_UP :: Bool -> Location -> Bool
round_sign_UP s l =
  case l of {
   Loc_Exact -> False;
   Loc_Inexact _ -> negb s}

round_N :: Bool -> Location -> Bool
round_N p l =
  case l of {
   Loc_Exact -> False;
   Loc_Inexact c -> case c of {
                     Eq -> p;
                     Lt -> False;
                     Gt -> True}}

data Full_float =
   F754_zero Bool
 | F754_infinity Bool
 | F754_nan Bool Positive
 | F754_finite Bool Positive Z

data Binary_float =
   B754_zero Bool
 | B754_infinity Bool
 | B754_nan Bool Positive
 | B754_finite Bool Positive Z

fF2B :: Z -> Z -> Full_float -> Binary_float
fF2B _ _ x =
  case x of {
   F754_zero s -> B754_zero s;
   F754_infinity s -> B754_infinity s;
   F754_nan b pl -> B754_nan b pl;
   F754_finite s m e -> B754_finite s m e}

bsign :: Z -> Z -> Binary_float -> Bool
bsign _ _ x =
  case x of {
   B754_zero s -> s;
   B754_infinity s -> s;
   B754_nan s _ -> s;
   B754_finite s _ _ -> s}

is_nan :: Z -> Z -> Binary_float -> Bool
is_nan _ _ f =
  case f of {
   B754_nan _ _ -> True;
   _ -> False}

get_nan_pl :: Z -> Z -> Binary_float -> Positive
get_nan_pl _ _ x =
  case x of {
   B754_nan _ pl -> pl;
   _ -> XH}

build_nan :: Z -> Z -> Binary_float -> Binary_float
build_nan prec1 emax1 x =
  B754_nan (bsign prec1 emax1 (proj1_sig x))
    (get_nan_pl prec1 emax1 (proj1_sig x))

bopp :: Z -> Z -> (Binary_float -> Binary_float) -> Binary_float ->
        Binary_float
bopp prec1 emax1 opp_nan x =
  case x of {
   B754_zero sx -> B754_zero (negb sx);
   B754_infinity sx -> B754_infinity (negb sx);
   B754_nan _ _ -> build_nan prec1 emax1 (opp_nan x);
   B754_finite sx mx ex -> B754_finite (negb sx) mx ex}

bcompare :: Z -> Z -> Binary_float -> Binary_float -> Option Comparison
bcompare _ _ f1 f2 =
  case f1 of {
   B754_zero _ ->
    case f2 of {
     B754_zero _ -> Some Eq;
     B754_infinity s -> Some (case s of {
                               True -> Gt;
                               False -> Lt});
     B754_nan _ _ -> None;
     B754_finite s _ _ -> Some (case s of {
                                 True -> Gt;
                                 False -> Lt})};
   B754_infinity s ->
    case f2 of {
     B754_infinity s0 -> Some
      (case s of {
        True -> case s0 of {
                 True -> Eq;
                 False -> Lt};
        False -> case s0 of {
                  True -> Gt;
                  False -> Eq}});
     B754_nan _ _ -> None;
     _ -> Some (case s of {
                 True -> Lt;
                 False -> Gt})};
   B754_nan _ _ -> None;
   B754_finite s1 m1 e1 ->
    case f2 of {
     B754_zero _ -> Some (case s1 of {
                           True -> Lt;
                           False -> Gt});
     B754_infinity s -> Some (case s of {
                               True -> Gt;
                               False -> Lt});
     B754_nan _ _ -> None;
     B754_finite s2 m2 e2 -> Some
      (case s1 of {
        True ->
         case s2 of {
          True ->
           case compare1 e1 e2 of {
            Eq -> compOpp (compare_cont Eq m1 m2);
            Lt -> Gt;
            Gt -> Lt};
          False -> Lt};
        False ->
         case s2 of {
          True -> Gt;
          False ->
           case compare1 e1 e2 of {
            Eq -> compare_cont Eq m1 m2;
            x -> x}}})}}

data Shr_record =
   Build_shr_record Z Bool Bool

shr_m :: Shr_record -> Z
shr_m s =
  case s of {
   Build_shr_record shr_m0 _ _ -> shr_m0}

shr_1 :: Shr_record -> Shr_record
shr_1 mrs =
  case mrs of {
   Build_shr_record m r s ->
    let {s0 = orb r s} in
    case m of {
     Z0 -> Build_shr_record Z0 False s0;
     Zpos p1 ->
      case p1 of {
       XI p -> Build_shr_record (Zpos p) True s0;
       XO p -> Build_shr_record (Zpos p) False s0;
       XH -> Build_shr_record Z0 True s0};
     Zneg p1 ->
      case p1 of {
       XI p -> Build_shr_record (Zneg p) True s0;
       XO p -> Build_shr_record (Zneg p) False s0;
       XH -> Build_shr_record Z0 True s0}}}

loc_of_shr_record :: Shr_record -> Location
loc_of_shr_record mrs =
  case mrs of {
   Build_shr_record _ shr_r shr_s ->
    case shr_r of {
     True -> case shr_s of {
              True -> Loc_Inexact Gt;
              False -> Loc_Inexact Eq};
     False -> case shr_s of {
               True -> Loc_Inexact Lt;
               False -> Loc_Exact}}}

shr_record_of_loc :: Z -> Location -> Shr_record
shr_record_of_loc m l =
  case l of {
   Loc_Exact -> Build_shr_record m False False;
   Loc_Inexact c ->
    case c of {
     Eq -> Build_shr_record m True False;
     Lt -> Build_shr_record m False True;
     Gt -> Build_shr_record m True True}}

shr :: Shr_record -> Z -> Z -> Prod Shr_record Z
shr mrs e n =
  case n of {
   Zpos p -> Pair (iter_pos shr_1 p mrs) (add3 e n);
   _ -> Pair mrs e}

shr_fexp :: Z -> Z -> Z -> Z -> Location -> Prod Shr_record Z
shr_fexp prec1 emax1 =
  let {emin = sub2 (sub2 (Zpos (XI XH)) emax1) prec1} in
  let {fexp = fLT_exp emin prec1} in
  (\m e l ->
  shr (shr_record_of_loc m l) e (sub2 (fexp (add3 (zdigits2 m) e)) e))

data Mode =
   Mode_NE
 | Mode_ZR
 | Mode_DN
 | Mode_UP
 | Mode_NA

choice_mode :: Mode -> Bool -> Z -> Location -> Z
choice_mode m sx mx lx =
  case m of {
   Mode_NE -> cond_incr (round_N (negb (even mx)) lx) mx;
   Mode_ZR -> mx;
   Mode_DN -> cond_incr (round_sign_DN sx lx) mx;
   Mode_UP -> cond_incr (round_sign_UP sx lx) mx;
   Mode_NA -> cond_incr (round_N True lx) mx}

overflow_to_inf :: Mode -> Bool -> Bool
overflow_to_inf m s =
  case m of {
   Mode_ZR -> False;
   Mode_DN -> s;
   Mode_UP -> negb s;
   _ -> True}

binary_overflow :: Z -> Z -> Mode -> Bool -> Full_float
binary_overflow prec1 emax1 m s =
  case overflow_to_inf m s of {
   True -> F754_infinity s;
   False -> F754_finite s
    (case sub2 (pow (Zpos (XO XH)) prec1) (Zpos XH) of {
      Zpos p -> p;
      _ -> XH}) (sub2 emax1 prec1)}

binary_round_aux :: Z -> Z -> Mode -> Bool -> Z -> Z -> Location ->
                    Full_float
binary_round_aux prec1 emax1 mode sx mx ex lx =
  case shr_fexp prec1 emax1 mx ex lx of {
   Pair mrs' e' ->
    case shr_fexp prec1 emax1
           (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e'
           Loc_Exact of {
     Pair mrs'' e'' ->
      case shr_m mrs'' of {
       Z0 -> F754_zero sx;
       Zpos m ->
        case leb1 e'' (sub2 emax1 prec1) of {
         True -> F754_finite sx m e'';
         False -> binary_overflow prec1 emax1 mode sx};
       Zneg _ -> F754_nan False XH}}}

bmult :: Z -> Z -> (Binary_float -> Binary_float -> Binary_float) -> Mode ->
         Binary_float -> Binary_float -> Binary_float
bmult prec1 emax1 mult_nan m x y =
  case x of {
   B754_zero sx ->
    case y of {
     B754_zero sy -> B754_zero (xorb sx sy);
     B754_finite sy _ _ -> B754_zero (xorb sx sy);
     _ -> build_nan prec1 emax1 (mult_nan x y)};
   B754_infinity sx ->
    case y of {
     B754_infinity sy -> B754_infinity (xorb sx sy);
     B754_finite sy _ _ -> B754_infinity (xorb sx sy);
     _ -> build_nan prec1 emax1 (mult_nan x y)};
   B754_nan _ _ -> build_nan prec1 emax1 (mult_nan x y);
   B754_finite sx mx ex ->
    case y of {
     B754_zero sy -> B754_zero (xorb sx sy);
     B754_infinity sy -> B754_infinity (xorb sx sy);
     B754_nan _ _ -> build_nan prec1 emax1 (mult_nan x y);
     B754_finite sy my ey ->
      fF2B prec1 emax1
        (binary_round_aux prec1 emax1 m (xorb sx sy) (Zpos (mul mx my))
          (add3 ex ey) Loc_Exact)}}

shl_align :: Positive -> Z -> Z -> Prod Positive Z
shl_align mx ex ex' =
  case sub2 ex' ex of {
   Zneg d -> Pair (shift_pos d mx) ex';
   _ -> Pair mx ex}

shl_align_fexp :: Z -> Z -> Positive -> Z -> Prod Positive Z
shl_align_fexp prec1 emax1 =
  let {emin = sub2 (sub2 (Zpos (XI XH)) emax1) prec1} in
  let {fexp = fLT_exp emin prec1} in
  (\mx ex -> shl_align mx ex (fexp (add3 (Zpos (digits2_pos mx)) ex)))

binary_round :: Z -> Z -> Mode -> Bool -> Positive -> Z -> Full_float
binary_round prec1 emax1 m sx mx ex =
  case shl_align_fexp prec1 emax1 mx ex of {
   Pair mz ez -> binary_round_aux prec1 emax1 m sx (Zpos mz) ez Loc_Exact}

binary_normalize :: Z -> Z -> Mode -> Z -> Z -> Bool -> Binary_float
binary_normalize prec1 emax1 mode m e szero =
  case m of {
   Z0 -> B754_zero szero;
   Zpos m0 -> fF2B prec1 emax1 (binary_round prec1 emax1 mode False m0 e);
   Zneg m0 -> fF2B prec1 emax1 (binary_round prec1 emax1 mode True m0 e)}

bplus :: Z -> Z -> (Binary_float -> Binary_float -> Binary_float) -> Mode ->
         Binary_float -> Binary_float -> Binary_float
bplus prec1 emax1 plus_nan m x y =
  case x of {
   B754_zero sx ->
    case y of {
     B754_zero sy ->
      case eqb sx sy of {
       True -> x;
       False -> case m of {
                 Mode_DN -> B754_zero True;
                 _ -> B754_zero False}};
     B754_nan _ _ -> build_nan prec1 emax1 (plus_nan x y);
     _ -> y};
   B754_infinity sx ->
    case y of {
     B754_infinity sy ->
      case eqb sx sy of {
       True -> x;
       False -> build_nan prec1 emax1 (plus_nan x y)};
     B754_nan _ _ -> build_nan prec1 emax1 (plus_nan x y);
     _ -> x};
   B754_nan _ _ -> build_nan prec1 emax1 (plus_nan x y);
   B754_finite sx mx ex ->
    case y of {
     B754_zero _ -> x;
     B754_infinity _ -> y;
     B754_nan _ _ -> build_nan prec1 emax1 (plus_nan x y);
     B754_finite sy my ey ->
      let {ez = min ex ey} in
      binary_normalize prec1 emax1 m
        (add3 (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
          (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))) ez
        (case m of {
          Mode_DN -> True;
          _ -> False})}}

bminus :: Z -> Z -> (Binary_float -> Binary_float -> Binary_float) -> Mode ->
          Binary_float -> Binary_float -> Binary_float
bminus prec1 emax1 minus_nan m x y =
  case x of {
   B754_zero sx ->
    case y of {
     B754_zero sy ->
      case eqb sx (negb sy) of {
       True -> x;
       False -> case m of {
                 Mode_DN -> B754_zero True;
                 _ -> B754_zero False}};
     B754_infinity sy -> B754_infinity (negb sy);
     B754_nan _ _ -> build_nan prec1 emax1 (minus_nan x y);
     B754_finite sy my ey -> B754_finite (negb sy) my ey};
   B754_infinity sx ->
    case y of {
     B754_infinity sy ->
      case eqb sx (negb sy) of {
       True -> x;
       False -> build_nan prec1 emax1 (minus_nan x y)};
     B754_nan _ _ -> build_nan prec1 emax1 (minus_nan x y);
     _ -> x};
   B754_nan _ _ -> build_nan prec1 emax1 (minus_nan x y);
   B754_finite sx mx ex ->
    case y of {
     B754_zero _ -> x;
     B754_infinity sy -> B754_infinity (negb sy);
     B754_nan _ _ -> build_nan prec1 emax1 (minus_nan x y);
     B754_finite sy my ey ->
      let {ez = min ex ey} in
      binary_normalize prec1 emax1 m
        (sub2 (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
          (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))) ez
        (case m of {
          Mode_DN -> True;
          _ -> False})}}

fdiv_core_binary :: Z -> Z -> Z -> Z -> Z -> Z -> Prod (Prod Z Z) Location
fdiv_core_binary prec1 emax1 =
  let {emin = sub2 (sub2 (Zpos (XI XH)) emax1) prec1} in
  let {fexp = fLT_exp emin prec1} in
  (\m1 e1 m2 e2 ->
  let {d1 = zdigits2 m1} in
  let {d2 = zdigits2 m2} in
  let {e' = min (fexp (sub2 (add3 d1 e1) (add3 d2 e2))) (sub2 e1 e2)} in
  let {s = sub2 (sub2 e1 e2) e'} in
  let {m' = case s of {
             Z0 -> m1;
             Zpos _ -> shiftl m1 s;
             Zneg _ -> Z0}} in
  case zfast_div_eucl m' m2 of {
   Pair q r -> Pair (Pair q e') (new_location m2 r Loc_Exact)})

bdiv :: Z -> Z -> (Binary_float -> Binary_float -> Binary_float) -> Mode ->
        Binary_float -> Binary_float -> Binary_float
bdiv prec1 emax1 div_nan m x y =
  case x of {
   B754_zero sx ->
    case y of {
     B754_infinity sy -> B754_zero (xorb sx sy);
     B754_finite sy _ _ -> B754_zero (xorb sx sy);
     _ -> build_nan prec1 emax1 (div_nan x y)};
   B754_infinity sx ->
    case y of {
     B754_zero sy -> B754_infinity (xorb sx sy);
     B754_finite sy _ _ -> B754_infinity (xorb sx sy);
     _ -> build_nan prec1 emax1 (div_nan x y)};
   B754_nan _ _ -> build_nan prec1 emax1 (div_nan x y);
   B754_finite sx mx ex ->
    case y of {
     B754_zero sy -> B754_infinity (xorb sx sy);
     B754_infinity sy -> B754_zero (xorb sx sy);
     B754_nan _ _ -> build_nan prec1 emax1 (div_nan x y);
     B754_finite sy my ey ->
      fF2B prec1 emax1
        (case fdiv_core_binary prec1 emax1 (Zpos mx) ex (Zpos my) ey of {
          Pair p lz ->
           case p of {
            Pair mz ez ->
             binary_round_aux prec1 emax1 m (xorb sx sy) mz ez lz}})}}

fsqrt_core_binary :: Z -> Z -> Z -> Z -> Prod (Prod Z Z) Location
fsqrt_core_binary prec1 emax1 =
  let {emin = sub2 (sub2 (Zpos (XI XH)) emax1) prec1} in
  let {fexp = fLT_exp emin prec1} in
  (\m e ->
  let {d = zdigits2 m} in
  let {e' = min (fexp (div1 (add3 (add3 d e) (Zpos XH)))) (div1 e)} in
  let {s = sub2 e (mul1 (Zpos (XO XH)) e')} in
  let {m' = case s of {
             Z0 -> m;
             Zpos _ -> shiftl m s;
             Zneg _ -> Z0}} in
  case sqrtrem0 m' of {
   Pair q r ->
    let {
     l = case zeq_bool r Z0 of {
          True -> Loc_Exact;
          False -> Loc_Inexact (case leb1 r q of {
                                 True -> Lt;
                                 False -> Gt})}}
    in
    Pair (Pair q e') l})

bsqrt :: Z -> Z -> (Binary_float -> Binary_float) -> Mode -> Binary_float ->
         Binary_float
bsqrt prec1 emax1 sqrt_nan m x =
  case x of {
   B754_zero _ -> x;
   B754_infinity s ->
    case s of {
     True -> build_nan prec1 emax1 (sqrt_nan x);
     False -> x};
   B754_nan _ _ -> build_nan prec1 emax1 (sqrt_nan x);
   B754_finite sx mx ex ->
    case sx of {
     True -> build_nan prec1 emax1 (sqrt_nan x);
     False ->
      fF2B prec1 emax1
        (case fsqrt_core_binary prec1 emax1 (Zpos mx) ex of {
          Pair p lz ->
           case p of {
            Pair mz ez -> binary_round_aux prec1 emax1 m False mz ez lz}})}}

join_bits :: Z -> Z -> Bool -> Z -> Z -> Z
join_bits mw ew s m e =
  add3
    (shiftl
      (add3 (case s of {
              True -> pow (Zpos (XO XH)) ew;
              False -> Z0}) e) mw) m

split_bits :: Z -> Z -> Z -> Prod (Prod Bool Z) Z
split_bits mw ew x =
  let {mm = pow (Zpos (XO XH)) mw} in
  let {em = pow (Zpos (XO XH)) ew} in
  Pair (Pair (leb1 (mul1 mm em) x) (modulo x mm)) (modulo (div0 x mm) em)

bits_of_binary_float :: Z -> Z -> Binary_float -> Z
bits_of_binary_float mw ew =
  let {emax1 = pow (Zpos (XO XH)) (sub2 ew (Zpos XH))} in
  let {prec1 = add3 mw (Zpos XH)} in
  let {emin = sub2 (sub2 (Zpos (XI XH)) emax1) prec1} in
  (\x ->
  case x of {
   B754_zero sx -> join_bits mw ew sx Z0 Z0;
   B754_infinity sx ->
    join_bits mw ew sx Z0 (sub2 (pow (Zpos (XO XH)) ew) (Zpos XH));
   B754_nan sx plx ->
    join_bits mw ew sx (Zpos plx) (sub2 (pow (Zpos (XO XH)) ew) (Zpos XH));
   B754_finite sx mx ex ->
    let {m = sub2 (Zpos mx) (pow (Zpos (XO XH)) mw)} in
    case leb1 Z0 m of {
     True -> join_bits mw ew sx m (add3 (sub2 ex emin) (Zpos XH));
     False -> join_bits mw ew sx (Zpos mx) Z0}})

binary_float_of_bits_aux :: Z -> Z -> Z -> Full_float
binary_float_of_bits_aux mw ew =
  let {emax1 = pow (Zpos (XO XH)) (sub2 ew (Zpos XH))} in
  let {prec1 = add3 mw (Zpos XH)} in
  let {emin = sub2 (sub2 (Zpos (XI XH)) emax1) prec1} in
  (\x ->
  case split_bits mw ew x of {
   Pair p ex ->
    case p of {
     Pair sx mx ->
      case zeq_bool ex Z0 of {
       True ->
        case mx of {
         Z0 -> F754_zero sx;
         Zpos px -> F754_finite sx px emin;
         Zneg _ -> F754_nan False XH};
       False ->
        case zeq_bool ex (sub2 (pow (Zpos (XO XH)) ew) (Zpos XH)) of {
         True ->
          case mx of {
           Z0 -> F754_infinity sx;
           Zpos plx -> F754_nan sx plx;
           Zneg _ -> F754_nan False XH};
         False ->
          case add3 mx (pow (Zpos (XO XH)) mw) of {
           Zpos px -> F754_finite sx px (sub2 (add3 ex emin) (Zpos XH));
           _ -> F754_nan False XH}}}}})

binary_float_of_bits :: Z -> Z -> Z -> Binary_float
binary_float_of_bits mw ew x =
  let {emax1 = pow (Zpos (XO XH)) (sub2 ew (Zpos XH))} in
  let {prec1 = add3 mw (Zpos XH)} in
  fF2B prec1 emax1 (binary_float_of_bits_aux mw ew x)

type Binary32 = Binary_float

default_nan_pl32 :: Binary32
default_nan_pl32 =
  B754_nan False
    (iter_nat (\x -> XO x) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S O)))))))))))))))))))))) XH)

b32_of_bits :: Z -> Binary32
b32_of_bits =
  binary_float_of_bits (Zpos (XI (XI (XI (XO XH))))) (Zpos (XO (XO (XO XH))))

bits_of_b32 :: Binary32 -> Z
bits_of_b32 =
  bits_of_binary_float (Zpos (XI (XI (XI (XO XH))))) (Zpos (XO (XO (XO XH))))

type Binary64 = Binary_float

default_nan_pl64 :: Binary64
default_nan_pl64 =
  B754_nan False
    (iter_nat (\x -> XO x) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))) XH)

b64_of_bits :: Z -> Binary64
b64_of_bits =
  binary_float_of_bits (Zpos (XO (XO (XI (XO (XI XH)))))) (Zpos (XI (XI (XO
    XH))))

bits_of_b64 :: Binary64 -> Z
bits_of_b64 =
  bits_of_binary_float (Zpos (XO (XO (XI (XO (XI XH)))))) (Zpos (XI (XI (XO
    XH))))

big_endian :: Bool
big_endian =
  False

default_nan_64 :: Prod Bool Positive
default_nan_64 =
  Pair True
    (nat_rect XH (\_ x -> XO x) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))

default_nan_32 :: Prod Bool Positive
default_nan_32 =
  Pair True
    (nat_rect XH (\_ x -> XO x) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O)))))))))))))))))))))))

choose_nan_64 :: (List (Prod Bool Positive)) -> Prod Bool Positive
choose_nan_64 l =
  case l of {
   Nil -> default_nan_64;
   Cons n _ -> n}

choose_nan_32 :: (List (Prod Bool Positive)) -> Prod Bool Positive
choose_nan_32 l =
  case l of {
   Nil -> default_nan_32;
   Cons n _ -> n}

data Comparison0 =
   Ceq
 | Cne
 | Clt
 | Cle
 | Cgt
 | Cge

wordsize :: Nat
wordsize =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))

wordsize0 :: Nat
wordsize0 =
  wordsize

zwordsize :: Z
zwordsize =
  of_nat1 wordsize0

modulus :: Z
modulus =
  two_power_nat wordsize0

half_modulus :: Z
half_modulus =
  div0 modulus (Zpos (XO XH))

max_unsigned :: Z
max_unsigned =
  sub2 modulus (Zpos XH)

max_signed :: Z
max_signed =
  sub2 half_modulus (Zpos XH)

min_signed :: Z
min_signed =
  opp half_modulus

type Int = Z
  -- singleton inductive, whose constructor was mkint
  
intval :: Int -> Z
intval i =
  i

z_mod_modulus :: Z -> Z
z_mod_modulus x =
  case x of {
   Z0 -> Z0;
   Zpos p -> p_mod_two_p p wordsize0;
   Zneg p ->
    let {r = p_mod_two_p p wordsize0} in
    case zeq r Z0 of {
     Left -> Z0;
     Right -> sub2 modulus r}}

unsigned :: Int -> Z
unsigned =
  intval

signed :: Int -> Z
signed n =
  let {x = unsigned n} in
  case zlt x half_modulus of {
   Left -> x;
   Right -> sub2 x modulus}

repr :: Z -> Int
repr =
  z_mod_modulus

zero :: Int
zero =
  repr Z0

one :: Int
one =
  repr (Zpos XH)

mone :: Int
mone =
  repr (Zneg XH)

iwordsize :: Int
iwordsize =
  repr zwordsize

eq_dec1 :: Int -> Int -> Sumbool
eq_dec1 =
  zeq

eq :: Int -> Int -> Bool
eq x y =
  case zeq (unsigned x) (unsigned y) of {
   Left -> True;
   Right -> False}

lt :: Int -> Int -> Bool
lt x y =
  case zlt (signed x) (signed y) of {
   Left -> True;
   Right -> False}

ltu :: Int -> Int -> Bool
ltu x y =
  case zlt (unsigned x) (unsigned y) of {
   Left -> True;
   Right -> False}

neg :: Int -> Int
neg x =
  repr (opp (unsigned x))

add5 :: Int -> Int -> Int
add5 x y =
  repr (add3 (unsigned x) (unsigned y))

sub3 :: Int -> Int -> Int
sub3 x y =
  repr (sub2 (unsigned x) (unsigned y))

mul2 :: Int -> Int -> Int
mul2 x y =
  repr (mul1 (unsigned x) (unsigned y))

divs :: Int -> Int -> Int
divs x y =
  repr (quot (signed x) (signed y))

mods :: Int -> Int -> Int
mods x y =
  repr (rem (signed x) (signed y))

divu :: Int -> Int -> Int
divu x y =
  repr (div0 (unsigned x) (unsigned y))

modu :: Int -> Int -> Int
modu x y =
  repr (modulo (unsigned x) (unsigned y))

and :: Int -> Int -> Int
and x y =
  repr (land1 (unsigned x) (unsigned y))

or :: Int -> Int -> Int
or x y =
  repr (lor1 (unsigned x) (unsigned y))

xor :: Int -> Int -> Int
xor x y =
  repr (lxor1 (unsigned x) (unsigned y))

not :: Int -> Int
not x =
  xor x mone

shl :: Int -> Int -> Int
shl x y =
  repr (shiftl (unsigned x) (unsigned y))

shru :: Int -> Int -> Int
shru x y =
  repr (shiftr (unsigned x) (unsigned y))

shr0 :: Int -> Int -> Int
shr0 x y =
  repr (shiftr (signed x) (unsigned y))

rol :: Int -> Int -> Int
rol x y =
  let {n = modulo (unsigned y) zwordsize} in
  repr
    (lor1 (shiftl (unsigned x) n) (shiftr (unsigned x) (sub2 zwordsize n)))

ror :: Int -> Int -> Int
ror x y =
  let {n = modulo (unsigned y) zwordsize} in
  repr
    (lor1 (shiftr (unsigned x) n) (shiftl (unsigned x) (sub2 zwordsize n)))

rolm :: Int -> Int -> Int -> Int
rolm x a m =
  and (rol x a) m

shrx :: Int -> Int -> Int
shrx x y =
  divs x (shl one y)

mulhu :: Int -> Int -> Int
mulhu x y =
  repr (div0 (mul1 (unsigned x) (unsigned y)) modulus)

mulhs :: Int -> Int -> Int
mulhs x y =
  repr (div0 (mul1 (signed x) (signed y)) modulus)

negative :: Int -> Int
negative x =
  case lt x zero of {
   True -> one;
   False -> zero}

add_carry0 :: Int -> Int -> Int -> Int
add_carry0 x y cin =
  case zlt (add3 (add3 (unsigned x) (unsigned y)) (unsigned cin)) modulus of {
   Left -> zero;
   Right -> one}

add_overflow :: Int -> Int -> Int -> Int
add_overflow x y cin =
  let {s = add3 (add3 (signed x) (signed y)) (signed cin)} in
  case andb (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed)) of {
   True -> zero;
   False -> one}

sub_borrow :: Int -> Int -> Int -> Int
sub_borrow x y bin =
  case zlt (sub2 (sub2 (unsigned x) (unsigned y)) (unsigned bin)) Z0 of {
   Left -> one;
   Right -> zero}

sub_overflow :: Int -> Int -> Int -> Int
sub_overflow x y bin =
  let {s = sub2 (sub2 (signed x) (signed y)) (signed bin)} in
  case andb (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed)) of {
   True -> zero;
   False -> one}

shr_carry :: Int -> Int -> Int
shr_carry x y =
  case andb (lt x zero) (negb (eq (and x (sub3 (shl one y) one)) zero)) of {
   True -> one;
   False -> zero}

zero_ext :: Z -> Int -> Int
zero_ext n x =
  repr (zzero_ext n (unsigned x))

sign_ext :: Z -> Int -> Int
sign_ext n x =
  repr (zsign_ext n (unsigned x))

one_bits :: Int -> List Int
one_bits x =
  map repr (z_one_bits wordsize0 (unsigned x) Z0)

is_power2 :: Int -> Option Int
is_power2 x =
  case z_is_power2 (unsigned x) of {
   Some i -> Some (repr i);
   None -> None}

cmp :: Comparison0 -> Int -> Int -> Bool
cmp c x y =
  case c of {
   Ceq -> eq x y;
   Cne -> negb (eq x y);
   Clt -> lt x y;
   Cle -> negb (lt y x);
   Cgt -> lt y x;
   Cge -> negb (lt x y)}

cmpu :: Comparison0 -> Int -> Int -> Bool
cmpu c x y =
  case c of {
   Ceq -> eq x y;
   Cne -> negb (eq x y);
   Clt -> ltu x y;
   Cle -> negb (ltu y x);
   Cgt -> ltu y x;
   Cge -> negb (ltu x y)}

notbool :: Int -> Int
notbool x =
  case eq x zero of {
   True -> one;
   False -> zero}

divmodu2 :: Int -> Int -> Int -> Option (Prod Int Int)
divmodu2 nhi nlo d =
  case eq_dec1 d zero of {
   Left -> None;
   Right ->
    case div_eucl0 (add3 (mul1 (unsigned nhi) modulus) (unsigned nlo))
           (unsigned d) of {
     Pair q r ->
      case zle q max_unsigned of {
       Left -> Some (Pair (repr q) (repr r));
       Right -> None}}}

divmods2 :: Int -> Int -> Int -> Option (Prod Int Int)
divmods2 nhi nlo d =
  case eq_dec1 d zero of {
   Left -> None;
   Right ->
    case quotrem (add3 (mul1 (signed nhi) modulus) (unsigned nlo)) (signed d) of {
     Pair q r ->
      case andb (proj_sumbool (zle min_signed q))
             (proj_sumbool (zle q max_signed)) of {
       True -> Some (Pair (repr q) (repr r));
       False -> None}}}

testbit2 :: Int -> Z -> Bool
testbit2 x i =
  testbit1 (unsigned x) i

int_of_one_bits :: (List Int) -> Int
int_of_one_bits l =
  case l of {
   Nil -> zero;
   Cons a b -> add5 (shl one a) (int_of_one_bits b)}

no_overlap :: Int -> Z -> Int -> Z -> Bool
no_overlap ofs1 sz1 ofs2 sz2 =
  let {x1 = unsigned ofs1} in
  let {x2 = unsigned ofs2} in
  andb
    (andb (proj_sumbool (zlt (add3 x1 sz1) modulus))
      (proj_sumbool (zlt (add3 x2 sz2) modulus)))
    (orb (proj_sumbool (zle (add3 x1 sz1) x2))
      (proj_sumbool (zle (add3 x2 sz2) x1)))

size1 :: Int -> Z
size1 x =
  zsize (unsigned x)

unsigned_bitfield_extract :: Z -> Z -> Int -> Int
unsigned_bitfield_extract pos width n =
  zero_ext width (shru n (repr pos))

signed_bitfield_extract :: Z -> Z -> Int -> Int
signed_bitfield_extract pos width n =
  sign_ext width (shru n (repr pos))

bitfield_insert :: Z -> Z -> Int -> Int -> Int
bitfield_insert pos width n p =
  let {mask = shl (repr (sub2 (two_p width) (Zpos XH))) (repr pos)} in
  or (shl (zero_ext width p) (repr pos)) (and n (not mask))

wordsize1 :: Nat
wordsize1 =
  S (S (S (S (S (S (S (S O)))))))

wordsize2 :: Nat
wordsize2 =
  wordsize1

zwordsize0 :: Z
zwordsize0 =
  of_nat1 wordsize2

modulus0 :: Z
modulus0 =
  two_power_nat wordsize2

half_modulus0 :: Z
half_modulus0 =
  div0 modulus0 (Zpos (XO XH))

max_unsigned0 :: Z
max_unsigned0 =
  sub2 modulus0 (Zpos XH)

max_signed0 :: Z
max_signed0 =
  sub2 half_modulus0 (Zpos XH)

min_signed0 :: Z
min_signed0 =
  opp half_modulus0

type Int0 = Z
  -- singleton inductive, whose constructor was mkint
  
intval0 :: Int0 -> Z
intval0 i =
  i

z_mod_modulus0 :: Z -> Z
z_mod_modulus0 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> p_mod_two_p p wordsize2;
   Zneg p ->
    let {r = p_mod_two_p p wordsize2} in
    case zeq r Z0 of {
     Left -> Z0;
     Right -> sub2 modulus0 r}}

unsigned0 :: Int0 -> Z
unsigned0 =
  intval0

signed0 :: Int0 -> Z
signed0 n =
  let {x = unsigned0 n} in
  case zlt x half_modulus0 of {
   Left -> x;
   Right -> sub2 x modulus0}

repr0 :: Z -> Int0
repr0 =
  z_mod_modulus0

zero0 :: Int0
zero0 =
  repr0 Z0

one0 :: Int0
one0 =
  repr0 (Zpos XH)

mone0 :: Int0
mone0 =
  repr0 (Zneg XH)

iwordsize0 :: Int0
iwordsize0 =
  repr0 zwordsize0

eq_dec2 :: Int0 -> Int0 -> Sumbool
eq_dec2 =
  zeq

eq0 :: Int0 -> Int0 -> Bool
eq0 x y =
  case zeq (unsigned0 x) (unsigned0 y) of {
   Left -> True;
   Right -> False}

lt0 :: Int0 -> Int0 -> Bool
lt0 x y =
  case zlt (signed0 x) (signed0 y) of {
   Left -> True;
   Right -> False}

ltu0 :: Int0 -> Int0 -> Bool
ltu0 x y =
  case zlt (unsigned0 x) (unsigned0 y) of {
   Left -> True;
   Right -> False}

neg0 :: Int0 -> Int0
neg0 x =
  repr0 (opp (unsigned0 x))

add6 :: Int0 -> Int0 -> Int0
add6 x y =
  repr0 (add3 (unsigned0 x) (unsigned0 y))

sub4 :: Int0 -> Int0 -> Int0
sub4 x y =
  repr0 (sub2 (unsigned0 x) (unsigned0 y))

mul3 :: Int0 -> Int0 -> Int0
mul3 x y =
  repr0 (mul1 (unsigned0 x) (unsigned0 y))

divs0 :: Int0 -> Int0 -> Int0
divs0 x y =
  repr0 (quot (signed0 x) (signed0 y))

mods0 :: Int0 -> Int0 -> Int0
mods0 x y =
  repr0 (rem (signed0 x) (signed0 y))

divu0 :: Int0 -> Int0 -> Int0
divu0 x y =
  repr0 (div0 (unsigned0 x) (unsigned0 y))

modu0 :: Int0 -> Int0 -> Int0
modu0 x y =
  repr0 (modulo (unsigned0 x) (unsigned0 y))

and0 :: Int0 -> Int0 -> Int0
and0 x y =
  repr0 (land1 (unsigned0 x) (unsigned0 y))

or0 :: Int0 -> Int0 -> Int0
or0 x y =
  repr0 (lor1 (unsigned0 x) (unsigned0 y))

xor0 :: Int0 -> Int0 -> Int0
xor0 x y =
  repr0 (lxor1 (unsigned0 x) (unsigned0 y))

not0 :: Int0 -> Int0
not0 x =
  xor0 x mone0

shl0 :: Int0 -> Int0 -> Int0
shl0 x y =
  repr0 (shiftl (unsigned0 x) (unsigned0 y))

shru0 :: Int0 -> Int0 -> Int0
shru0 x y =
  repr0 (shiftr (unsigned0 x) (unsigned0 y))

shr1 :: Int0 -> Int0 -> Int0
shr1 x y =
  repr0 (shiftr (signed0 x) (unsigned0 y))

rol0 :: Int0 -> Int0 -> Int0
rol0 x y =
  let {n = modulo (unsigned0 y) zwordsize0} in
  repr0
    (lor1 (shiftl (unsigned0 x) n)
      (shiftr (unsigned0 x) (sub2 zwordsize0 n)))

ror0 :: Int0 -> Int0 -> Int0
ror0 x y =
  let {n = modulo (unsigned0 y) zwordsize0} in
  repr0
    (lor1 (shiftr (unsigned0 x) n)
      (shiftl (unsigned0 x) (sub2 zwordsize0 n)))

rolm0 :: Int0 -> Int0 -> Int0 -> Int0
rolm0 x a m =
  and0 (rol0 x a) m

shrx0 :: Int0 -> Int0 -> Int0
shrx0 x y =
  divs0 x (shl0 one0 y)

mulhu0 :: Int0 -> Int0 -> Int0
mulhu0 x y =
  repr0 (div0 (mul1 (unsigned0 x) (unsigned0 y)) modulus0)

mulhs0 :: Int0 -> Int0 -> Int0
mulhs0 x y =
  repr0 (div0 (mul1 (signed0 x) (signed0 y)) modulus0)

negative0 :: Int0 -> Int0
negative0 x =
  case lt0 x zero0 of {
   True -> one0;
   False -> zero0}

add_carry1 :: Int0 -> Int0 -> Int0 -> Int0
add_carry1 x y cin =
  case zlt (add3 (add3 (unsigned0 x) (unsigned0 y)) (unsigned0 cin)) modulus0 of {
   Left -> zero0;
   Right -> one0}

add_overflow0 :: Int0 -> Int0 -> Int0 -> Int0
add_overflow0 x y cin =
  let {s = add3 (add3 (signed0 x) (signed0 y)) (signed0 cin)} in
  case andb (proj_sumbool (zle min_signed0 s))
         (proj_sumbool (zle s max_signed0)) of {
   True -> zero0;
   False -> one0}

sub_borrow0 :: Int0 -> Int0 -> Int0 -> Int0
sub_borrow0 x y bin =
  case zlt (sub2 (sub2 (unsigned0 x) (unsigned0 y)) (unsigned0 bin)) Z0 of {
   Left -> one0;
   Right -> zero0}

sub_overflow0 :: Int0 -> Int0 -> Int0 -> Int0
sub_overflow0 x y bin =
  let {s = sub2 (sub2 (signed0 x) (signed0 y)) (signed0 bin)} in
  case andb (proj_sumbool (zle min_signed0 s))
         (proj_sumbool (zle s max_signed0)) of {
   True -> zero0;
   False -> one0}

shr_carry0 :: Int0 -> Int0 -> Int0
shr_carry0 x y =
  case andb (lt0 x zero0)
         (negb (eq0 (and0 x (sub4 (shl0 one0 y) one0)) zero0)) of {
   True -> one0;
   False -> zero0}

zero_ext0 :: Z -> Int0 -> Int0
zero_ext0 n x =
  repr0 (zzero_ext n (unsigned0 x))

sign_ext0 :: Z -> Int0 -> Int0
sign_ext0 n x =
  repr0 (zsign_ext n (unsigned0 x))

one_bits0 :: Int0 -> List Int0
one_bits0 x =
  map repr0 (z_one_bits wordsize2 (unsigned0 x) Z0)

is_power0 :: Int0 -> Option Int0
is_power0 x =
  case z_is_power2 (unsigned0 x) of {
   Some i -> Some (repr0 i);
   None -> None}

cmp0 :: Comparison0 -> Int0 -> Int0 -> Bool
cmp0 c x y =
  case c of {
   Ceq -> eq0 x y;
   Cne -> negb (eq0 x y);
   Clt -> lt0 x y;
   Cle -> negb (lt0 y x);
   Cgt -> lt0 y x;
   Cge -> negb (lt0 x y)}

cmpu0 :: Comparison0 -> Int0 -> Int0 -> Bool
cmpu0 c x y =
  case c of {
   Ceq -> eq0 x y;
   Cne -> negb (eq0 x y);
   Clt -> ltu0 x y;
   Cle -> negb (ltu0 y x);
   Cgt -> ltu0 y x;
   Cge -> negb (ltu0 x y)}

notbool0 :: Int0 -> Int0
notbool0 x =
  case eq0 x zero0 of {
   True -> one0;
   False -> zero0}

divmodu0 :: Int0 -> Int0 -> Int0 -> Option (Prod Int0 Int0)
divmodu0 nhi nlo d =
  case eq_dec2 d zero0 of {
   Left -> None;
   Right ->
    case div_eucl0 (add3 (mul1 (unsigned0 nhi) modulus0) (unsigned0 nlo))
           (unsigned0 d) of {
     Pair q r ->
      case zle q max_unsigned0 of {
       Left -> Some (Pair (repr0 q) (repr0 r));
       Right -> None}}}

divmods0 :: Int0 -> Int0 -> Int0 -> Option (Prod Int0 Int0)
divmods0 nhi nlo d =
  case eq_dec2 d zero0 of {
   Left -> None;
   Right ->
    case quotrem (add3 (mul1 (signed0 nhi) modulus0) (unsigned0 nlo))
           (signed0 d) of {
     Pair q r ->
      case andb (proj_sumbool (zle min_signed0 q))
             (proj_sumbool (zle q max_signed0)) of {
       True -> Some (Pair (repr0 q) (repr0 r));
       False -> None}}}

testbit3 :: Int0 -> Z -> Bool
testbit3 x i =
  testbit1 (unsigned0 x) i

int_of_one_bits0 :: (List Int0) -> Int0
int_of_one_bits0 l =
  case l of {
   Nil -> zero0;
   Cons a b -> add6 (shl0 one0 a) (int_of_one_bits0 b)}

no_overlap0 :: Int0 -> Z -> Int0 -> Z -> Bool
no_overlap0 ofs1 sz1 ofs2 sz2 =
  let {x1 = unsigned0 ofs1} in
  let {x2 = unsigned0 ofs2} in
  andb
    (andb (proj_sumbool (zlt (add3 x1 sz1) modulus0))
      (proj_sumbool (zlt (add3 x2 sz2) modulus0)))
    (orb (proj_sumbool (zle (add3 x1 sz1) x2))
      (proj_sumbool (zle (add3 x2 sz2) x1)))

size2 :: Int0 -> Z
size2 x =
  zsize (unsigned0 x)

unsigned_bitfield_extract0 :: Z -> Z -> Int0 -> Int0
unsigned_bitfield_extract0 pos width n =
  zero_ext0 width (shru0 n (repr0 pos))

signed_bitfield_extract0 :: Z -> Z -> Int0 -> Int0
signed_bitfield_extract0 pos width n =
  sign_ext0 width (shru0 n (repr0 pos))

bitfield_insert0 :: Z -> Z -> Int0 -> Int0 -> Int0
bitfield_insert0 pos width n p =
  let {mask = shl0 (repr0 (sub2 (two_p width) (Zpos XH))) (repr0 pos)} in
  or0 (shl0 (zero_ext0 width p) (repr0 pos)) (and0 n (not0 mask))

wordsize3 :: Nat
wordsize3 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

wordsize4 :: Nat
wordsize4 =
  wordsize3

modulus1 :: Z
modulus1 =
  two_power_nat wordsize4

type Int1 = Z
  -- singleton inductive, whose constructor was mkint
  
intval1 :: Int1 -> Z
intval1 i =
  i

z_mod_modulus1 :: Z -> Z
z_mod_modulus1 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> p_mod_two_p p wordsize4;
   Zneg p ->
    let {r = p_mod_two_p p wordsize4} in
    case zeq r Z0 of {
     Left -> Z0;
     Right -> sub2 modulus1 r}}

unsigned1 :: Int1 -> Z
unsigned1 =
  intval1

repr1 :: Z -> Int1
repr1 =
  z_mod_modulus1

type NotT t = t -> Empty_set

type DecidableT t = Sum t (NotT t)

type IffT a b = Prod (a -> b) (b -> a)

not_notT :: Empty_set
not_notT =
  Prelude.error "absurd case"

decidable_decidableT :: Decidable -> DecidableT ()
decidable_decidableT h =
  case h of {
   Left -> Inl __;
   Right -> Inr (\_ -> not_notT)}

decidableT_and :: (DecidableT a1) -> (DecidableT a2) -> DecidableT
                  (Prod a1 a2)
decidableT_and __top_assumption_ =
  let {
   _evar_0_ = \p1 __top_assumption_0 ->
    let {_evar_0_ = \p2 -> Inl (Pair p1 p2)} in
    let {
     _evar_0_0 = \np2 -> Inr (\__top_assumption_1 ->
      let {_evar_0_0 = \_ _b_ -> empty_set_rec (np2 _b_)} in
      case __top_assumption_1 of {
       Pair x x0 -> _evar_0_0 x x0})}
    in
    case __top_assumption_0 of {
     Inl x -> _evar_0_ x;
     Inr x -> _evar_0_0 x}}
  in
  let {
   _evar_0_0 = \np1 _ -> Inr (\__top_assumption_0 ->
    let {_evar_0_0 = \_a_ _ -> empty_set_rec (np1 _a_)} in
    case __top_assumption_0 of {
     Pair x x0 -> _evar_0_0 x x0})}
  in
  case __top_assumption_ of {
   Inl x -> _evar_0_ x;
   Inr x -> _evar_0_0 x}

decidableT_and_conj :: (DecidableT ()) -> (DecidableT ()) -> DecidableT ()
decidableT_and_conj __top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_0 ->
    let {_evar_0_ = \_ -> Inl __} in
    let {_evar_0_0 = \np2 -> Inr (\_ -> empty_set_rec (np2 __))} in
    case __top_assumption_0 of {
     Inl x -> _evar_0_ x;
     Inr x -> _evar_0_0 x}}
  in
  let {_evar_0_0 = \np1 _ -> Inr (\_ -> empty_set_rec (np1 __))} in
  case __top_assumption_ of {
   Inl _ -> _evar_0_;
   Inr x -> _evar_0_0 x}

decidableT_equiv :: (IffT a1 a2) -> (DecidableT a1) -> DecidableT a2
decidableT_equiv __top_assumption_ =
  let {
   _evar_0_ = \i1 i2 __top_assumption_0 ->
    let {_evar_0_ = \h -> Inl (i1 h)} in
    let {_evar_0_0 = \nH -> Inr (\x -> nH (i2 x))} in
    case __top_assumption_0 of {
     Inl x -> _evar_0_ x;
     Inr x -> _evar_0_0 x}}
  in
  case __top_assumption_ of {
   Pair x x0 -> _evar_0_ x x0}

is_true_decidableT :: Bool -> DecidableT ()
is_true_decidableT b =
  case b of {
   True -> Inl __;
   False -> Inr (\_ -> false_rec)}

type PickableT a p = Sum (SigT a p) (NotT (SigT a p))

type PickableT2 a1 a2 p =
  Sum (SigT (Prod a1 a2) Any) (NotT (SigT a1 (SigT a2 p)))

type PickableT3 a1 a2 a3 p =
  Sum (SigT (Prod (Prod a1 a2) a3) Any)
  (NotT (SigT a1 (SigT a2 (SigT a3 p))))

type PickableT4 a1 a2 a3 a4 p =
  Sum (SigT (Prod (Prod (Prod a1 a2) a3) a4) Any)
  (NotT (SigT a1 (SigT a2 (SigT a3 (SigT a4 p)))))

pickable_decidable_T :: (PickableT a1 a2) -> DecidableT (SigT a1 a2)
pickable_decidable_T __top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_0 ->
    let {_evar_0_ = \x p -> Inl (ExistT x p)} in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_ x x0}}
  in
  let {_evar_0_0 = \n -> Inr n} in
  case __top_assumption_ of {
   Inl x -> _evar_0_ x;
   Inr x -> _evar_0_0 x}

pickableT2_equiv :: (a1 -> a2 -> IffT a3 a4) -> (PickableT2 a1 a2 a3) ->
                    PickableT2 a1 a2 a4
pickableT2_equiv e __top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_0 ->
    let {
     _evar_0_ = \__top_assumption_1 ->
      let {
       _evar_0_ = \x1 x2 p -> Inl (ExistT (Pair x1 x2)
        (case e x1 x2 of {
          Pair x _ -> x p}))}
      in
      case __top_assumption_1 of {
       Pair x x0 -> _evar_0_ x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_ x x0}}
  in
  let {
   _evar_0_0 = \n -> Inr (\__top_assumption_0 ->
    let {
     _evar_0_0 = \x1 __top_assumption_1 ->
      let {
       _evar_0_0 = \x2 p ->
        n (ExistT x1 (ExistT x2 (case e x1 x2 of {
                                  Pair _ x -> x p})))}
      in
      case __top_assumption_1 of {
       ExistT x x0 -> _evar_0_0 x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_0 x x0})}
  in
  case __top_assumption_ of {
   Inl x -> unsafeCoerce _evar_0_ x;
   Inr x -> _evar_0_0 x}

pickable2_convert_T :: ((Prod a1 a2) -> Prod a3 a4) -> (a1 -> a2 -> a5 ->
                       Any) -> (a3 -> a4 -> a6 -> SigT a1 (SigT a2 a5)) ->
                       (PickableT2 a1 a2 a5) -> PickableT2 a3 a4 a6
pickable2_convert_T f e1 e2 __top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_0 ->
    let {
     _evar_0_ = \__top_assumption_1 ->
      let {_evar_0_ = \x1 x2 p -> Inl (ExistT (f (Pair x1 x2)) (e1 x1 x2 p))}
      in
      case __top_assumption_1 of {
       Pair x x0 -> _evar_0_ x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_ x x0}}
  in
  let {
   _evar_0_0 = \n -> Inr (\__top_assumption_0 ->
    let {
     _evar_0_0 = \x1 __top_assumption_1 ->
      let {
       _evar_0_0 = \x2 p ->
        n
          (let {__top_assumption_2 = e2 x1 x2 p} in
           let {
            _evar_0_0 = \a1 __top_assumption_3 ->
             let {_evar_0_0 = \a2 p' -> ExistT a1 (ExistT a2 p')} in
             case __top_assumption_3 of {
              ExistT x x0 -> _evar_0_0 x x0}}
           in
           case __top_assumption_2 of {
            ExistT x x0 -> _evar_0_0 x x0})}
      in
      case __top_assumption_1 of {
       ExistT x x0 -> _evar_0_0 x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_0 x x0})}
  in
  case __top_assumption_ of {
   Inl x -> unsafeCoerce _evar_0_ x;
   Inr x -> _evar_0_0 x}

pickable2_weaken_T :: (PickableT2 a1 a2 a3) -> PickableT a1 (SigT a2 a3)
pickable2_weaken_T __top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_0 ->
    let {
     _evar_0_ = \__top_assumption_1 ->
      let {_evar_0_ = \x1 x2 p -> Inl (ExistT x1 (ExistT x2 p))} in
      case __top_assumption_1 of {
       Pair x x0 -> _evar_0_ x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_ x x0}}
  in
  let {
   _evar_0_0 = \nE -> Inr (\__top_assumption_0 ->
    let {
     _evar_0_0 = \x1 __top_assumption_1 ->
      let {_evar_0_0 = \x2 p -> nE (ExistT x1 (ExistT x2 p))} in
      case __top_assumption_1 of {
       ExistT x x0 -> _evar_0_0 x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_0 x x0})}
  in
  case __top_assumption_ of {
   Inl x -> unsafeCoerce _evar_0_ x;
   Inr x -> _evar_0_0 x}

pickable3_weaken_T :: (PickableT3 a1 a2 a3 a4) -> PickableT2 a1 a2
                      (SigT a3 a4)
pickable3_weaken_T __top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_0 ->
    let {
     _evar_0_ = \__top_assumption_1 ->
      let {
       _evar_0_ = \__top_assumption_2 ->
        let {
         _evar_0_ = \x1 x2 x3 p -> Inl (ExistT (Pair x1 x2) (ExistT x3 p))}
        in
        case __top_assumption_2 of {
         Pair x x0 -> _evar_0_ x x0}}
      in
      case __top_assumption_1 of {
       Pair x x0 -> _evar_0_ x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_ x x0}}
  in
  let {
   _evar_0_0 = \nE -> Inr (\__top_assumption_0 ->
    let {
     _evar_0_0 = \x1 __top_assumption_1 ->
      let {
       _evar_0_0 = \x2 __top_assumption_2 ->
        let {_evar_0_0 = \x3 p -> nE (ExistT x1 (ExistT x2 (ExistT x3 p)))}
        in
        case __top_assumption_2 of {
         ExistT x x0 -> _evar_0_0 x x0}}
      in
      case __top_assumption_1 of {
       ExistT x x0 -> _evar_0_0 x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_0 x x0})}
  in
  case __top_assumption_ of {
   Inl x -> unsafeCoerce _evar_0_ x;
   Inr x -> _evar_0_0 x}

pickable4_weaken_T :: (PickableT4 a1 a2 a3 a4 a5) -> PickableT3 a1 a2 
                      a3 (SigT a4 a5)
pickable4_weaken_T __top_assumption_ =
  let {
   _evar_0_ = \__top_assumption_0 ->
    let {
     _evar_0_ = \__top_assumption_1 ->
      let {
       _evar_0_ = \__top_assumption_2 ->
        let {
         _evar_0_ = \__top_assumption_3 ->
          let {
           _evar_0_ = \x1 x2 x3 x4 p -> Inl (ExistT (Pair (Pair x1 x2) x3)
            (ExistT x4 p))}
          in
          case __top_assumption_3 of {
           Pair x x0 -> _evar_0_ x x0}}
        in
        case __top_assumption_2 of {
         Pair x x0 -> _evar_0_ x x0}}
      in
      case __top_assumption_1 of {
       Pair x x0 -> _evar_0_ x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_ x x0}}
  in
  let {
   _evar_0_0 = \nE -> Inr (\__top_assumption_0 ->
    let {
     _evar_0_0 = \x1 __top_assumption_1 ->
      let {
       _evar_0_0 = \x2 __top_assumption_2 ->
        let {
         _evar_0_0 = \x3 __top_assumption_3 ->
          let {
           _evar_0_0 = \x4 p ->
            nE (ExistT x1 (ExistT x2 (ExistT x3 (ExistT x4 p))))}
          in
          case __top_assumption_3 of {
           ExistT x x0 -> _evar_0_0 x x0}}
        in
        case __top_assumption_2 of {
         ExistT x x0 -> _evar_0_0 x x0}}
      in
      case __top_assumption_1 of {
       ExistT x x0 -> _evar_0_0 x x0}}
    in
    case __top_assumption_0 of {
     ExistT x x0 -> _evar_0_0 x x0})}
  in
  case __top_assumption_ of {
   Inl x -> unsafeCoerce _evar_0_ x;
   Inr x -> _evar_0_0 x}

z_eqP :: Axiom Z
z_eqP x y =
  let {_evar_0_ = \_ -> ReflectT} in
  let {_evar_0_0 = \_ -> ReflectF} in
  case zeq x y of {
   Left -> _evar_0_ __;
   Right -> _evar_0_0 __}

z_eqMixin :: Mixin_of Z
z_eqMixin =
  Mixin (\x y -> is_left (zeq x y)) z_eqP

z_eqType :: Type
z_eqType =
  unsafeCoerce z_eqMixin

pos_eqP :: Axiom Positive
pos_eqP x y =
  iff_reflect (eqb1 x y)

pos_eqMixin :: Mixin_of Positive
pos_eqMixin =
  Mixin eqb1 pos_eqP

pos_eqType :: Type
pos_eqType =
  unsafeCoerce pos_eqMixin

eq_dec_Equality_axiom :: (a1 -> a1 -> Sumbool) -> Axiom a1
eq_dec_Equality_axiom eq_dec5 x y =
  let {_evar_0_ = \_ -> ReflectT} in
  let {_evar_0_0 = \_ -> ReflectF} in
  case eq_dec5 x y of {
   Left -> _evar_0_ __;
   Right -> _evar_0_0 __}

data Forall a p =
   Forall_nil
 | Forall_cons a (List a) p (Forall a p)

forall_rect :: a3 -> (a1 -> (List a1) -> a2 -> (Forall a1 a2) -> a3 -> a3) ->
               (List a1) -> (Forall a1 a2) -> a3
forall_rect f f0 _ f1 =
  case f1 of {
   Forall_nil -> f;
   Forall_cons e l y f2 -> f0 e l y f2 (forall_rect f f0 l f2)}

max0 :: (List a1) -> (Forall a1 Nat) -> Nat
max0 _ f =
  case f of {
   Forall_nil -> O;
   Forall_cons _ l0 n f0 -> maxn n (max0 l0 f0)}

forall_forall_eq_dec :: (List a1) -> (List a1) -> (Forall a1 (a1 -> Sumbool))
                        -> Sumbool
forall_forall_eq_dec l1 _l2_ f =
  forall_rect (\__top_assumption_ ->
    let {_evar_0_ = Left} in
    let {_evar_0_0 = \_ _ _ -> Right} in
    list_rec _evar_0_ _evar_0_0 __top_assumption_)
    (\_ _ c _ iH __top_assumption_ ->
    let {_evar_0_ = Right} in
    let {
     _evar_0_0 = \e2 l2 ->
      let {s = c e2} in case s of {
                         Left -> iH l2;
                         Right -> Right}}
    in
    case __top_assumption_ of {
     Nil -> _evar_0_;
     Cons x x0 -> _evar_0_0 x x0}) l1 f _l2_

list_search_prefix_pickableT :: (Comparable a1) -> ((List a1) -> DecidableT
                                a2) -> (List a1) -> (List a1) -> PickableT
                                (List a1) (Prod () a2)
list_search_prefix_pickableT c _Hyp_ l =
  list_rect (\_ d l' ->
    case d l' of {
     Inl d0 -> Inl (ExistT l' (Pair __ d0));
     Inr d0 -> Inr (\__top_assumption_ ->
      let {
       _evar_0_ = \lf __top_assumption_0 ->
        let {
         _evar_0_ = \nd ->
          eq_rect_r (cat Nil lf) (\d1 -> empty_set_rec (d1 nd)) l' d0}
        in
        case __top_assumption_0 of {
         Pair _ x -> _evar_0_ x}}
      in
      case __top_assumption_ of {
       ExistT x x0 -> _evar_0_ x x0})}) (\a l0 iH _ d l' ->
    case l' of {
     Nil -> Inr (\__top_assumption_ ->
      let {
       _evar_0_ = \_ __top_assumption_0 ->
        let {_evar_0_ = \_ -> false_rec} in
        case __top_assumption_0 of {
         Pair _ x -> _evar_0_ x}}
      in
      case __top_assumption_ of {
       ExistT x x0 -> _evar_0_ x x0});
     Cons a' l'0 ->
      case c a a' of {
       Left ->
        eq_rect_r a'
          (case iH __ d l'0 of {
            Inl e -> Inl
             (case e of {
               ExistT lf p1 ->
                case p1 of {
                 Pair _ p -> ExistT lf
                  (let {_evar_0_ = Pair __ p} in
                   eq_rect_r (cat l0 lf) _evar_0_ l'0)}});
            Inr nE -> Inr (\__top_assumption_ ->
             let {
              _evar_0_ = \lf __top_assumption_0 ->
               let {
                _evar_0_ = \p ->
                 nE (ExistT lf (eq_rect_r (cat l0 lf) (Pair __ p) l'0))}
               in
               case __top_assumption_0 of {
                Pair _ x -> _evar_0_ x}}
             in
             case __top_assumption_ of {
              ExistT x x0 -> _evar_0_ x x0})}) a;
       Right -> Inr (\__top_assumption_ ->
        let {
         _evar_0_ = \lf __top_assumption_0 ->
          let {
           _evar_0_ = \_ ->
            eq_rec_r a (\_ ->
              eq_rec_r (cat l0 lf) (Prelude.error "absurd case") l'0) a' __}
          in
          case __top_assumption_0 of {
           Pair _ x -> _evar_0_ x}}
        in
        case __top_assumption_ of {
         ExistT x x0 -> _evar_0_ x x0})}}) l __ _Hyp_

list_split_pickableT2_gen :: (List a1) -> ((List a1) -> (List a1) -> () ->
                             DecidableT a2) -> PickableT2 (List a1) (List a1)
                             (Prod () a2)
list_split_pickableT2_gen l =
  list_rect (\_ d ->
    case d Nil Nil __ of {
     Inl y -> Inl (ExistT (Pair Nil Nil) (unsafeCoerce (Pair __ y)));
     Inr y -> Inr (\__top_assumption_ ->
      let {
       _evar_0_ = \l1 __top_assumption_0 ->
        let {
         _evar_0_ = \l2 __top_assumption_1 ->
          let {
           _evar_0_ = \p ->
            eq_rect_r Nil (\_ p1 ->
              eq_rect_r Nil (\p2 _ -> empty_set_rec (y p2)) l2 p1 __) l1 __ p}
          in
          case __top_assumption_1 of {
           Pair _ x -> _evar_0_ x}}
        in
        case __top_assumption_0 of {
         ExistT x x0 -> _evar_0_ x x0}}
      in
      case __top_assumption_ of {
       ExistT x x0 -> _evar_0_ x x0})}) (\a l0 iH _ d ->
    ssr_have (\l1 l2 _ -> d (Cons a l1) l2 __) (\da ->
      ssr_have
        (ssr_have
          (unsafeCoerce pickableT2_equiv (\l1 l2 -> Pair
            (\__top_assumption_ ->
            let {
             _evar_0_ = \p ->
              eq_rect_r (cat l1 l2) (\_ _ _ -> Pair __ p) l0 iH d da}
            in
            case __top_assumption_ of {
             Pair _ x -> _evar_0_ x}) (\__top_assumption_ ->
            let {_evar_0_ = \p -> eq_rect_r (cat l1 l2) (Pair __ p) l0} in
            case __top_assumption_ of {
             Pair _ x -> _evar_0_ x})) (iH __ da)) (\pa ->
          case pa of {
           Inl __top_assumption_ ->
            let {
             _evar_0_ = \__top_assumption_0 ->
              let {
               _evar_0_ = \l1 l2 __top_assumption_1 ->
                let {
                 _evar_0_ = \p -> Inl (ExistT (Pair (Cons a l1) l2) (Pair __
                  (Pair p __)))}
                in
                case __top_assumption_1 of {
                 Pair _ x -> _evar_0_ x}}
              in
              case __top_assumption_0 of {
               Pair x x0 -> _evar_0_ x x0}}
            in
            case __top_assumption_ of {
             ExistT x x0 -> _evar_0_ x x0};
           Inr ex -> Inr (\__top_assumption_ ->
            let {
             _evar_0_ = \l1 __top_assumption_0 ->
              let {
               _evar_0_ = \l2 __top_assumption_1 ->
                let {
                 _evar_0_ = \__top_assumption_2 ->
                  let {
                   _evar_0_ = \p ->
                    ex
                      (case l1 of {
                        Nil -> false_rect;
                        Cons a' l3 ->
                         eq_rect_r a' (\_ ->
                           eq_rect_r (cat l3 l2) (ExistT l3 (ExistT l2
                             (eq_rect_r a' (\d0 da0 pa0 _ ->
                               eq_rect_r (cat l3 l2) (\_ _ _ _ _ -> Pair __
                                 p) l0 iH pa0 da0 d0 __) a d da pa __))) l0)
                           a __})}
                  in
                  case __top_assumption_2 of {
                   Pair x _ -> _evar_0_ x}}
                in
                case __top_assumption_1 of {
                 Pair _ x -> _evar_0_ x}}
              in
              case __top_assumption_0 of {
               ExistT x x0 -> _evar_0_ x x0}}
            in
            case __top_assumption_ of {
             ExistT x x0 -> _evar_0_ x x0})})) (\pa ->
        case pa of {
         Inl __top_assumption_ ->
          let {
           _evar_0_ = \__top_assumption_0 ->
            let {
             _evar_0_ = \l1 l2 __top_assumption_1 ->
              let {
               _evar_0_ = \__top_assumption_2 ->
                let {_evar_0_ = \p -> Inl (ExistT (Pair l1 l2) (Pair __ p))}
                in
                case __top_assumption_2 of {
                 Pair x _ -> _evar_0_ x}}
              in
              case __top_assumption_1 of {
               Pair _ x -> _evar_0_ x}}
            in
            case __top_assumption_0 of {
             Pair x x0 -> _evar_0_ x x0}}
          in
          case __top_assumption_ of {
           ExistT x x0 -> unsafeCoerce _evar_0_ x x0};
         Inr nE ->
          case d Nil (Cons a l0) __ of {
           Inl p -> Inl (ExistT (Pair Nil (Cons a l0))
            (unsafeCoerce (Pair __ p)));
           Inr _ -> Inr (\__top_assumption_ ->
            let {
             _evar_0_ = \l1 __top_assumption_0 ->
              let {
               _evar_0_ = \l2 __top_assumption_1 ->
                let {
                 _evar_0_ = \p ->
                  nE (ExistT l1 (ExistT l2 (Pair __ (Pair p __))))}
                in
                case __top_assumption_1 of {
                 Pair _ x -> _evar_0_ x}}
              in
              case __top_assumption_0 of {
               ExistT x x0 -> _evar_0_ x x0}}
            in
            case __top_assumption_ of {
             ExistT x x0 -> _evar_0_ x x0})}}))) l __

list_split_pickableT2 :: ((List a1) -> (List a1) -> DecidableT a2) -> (List
                         a1) -> PickableT2 (List a1) (List a1) (Prod () a2)
list_split_pickableT2 d l =
  list_split_pickableT2_gen l (\l1 l2 _ -> d l1 l2)

list_search_split_pickableT2 :: (Comparable a1) -> ((List a1) -> (List 
                                a1) -> DecidableT a2) -> (List a1) -> (List
                                a1) -> PickableT2 (List a1) (List a1)
                                (Prod () a2)
list_search_split_pickableT2 c d l l' =
  pickable2_convert_T (\pat ->
    case pat of {
     Pair l1 l2 -> Pair l1 (drop (size0 l) l2)}) (\l1 l2 __top_assumption_ ->
    let {
     _evar_0_ = \__top_assumption_0 ->
      let {
       _evar_0_ = \l2' __top_assumption_1 ->
        let {
         _evar_0_ = \p ->
          eq_rect_r (cat l1 l2)
            (eq_rect_r (cat l l2')
              (let {
                _evar_0_ = ssr_have __ (\_ ->
                             let {
                              _evar_0_ = ssr_have __ (\_ ->
                                           let {
                                            _evar_0_ = let {
                                                        _evar_0_ = Pair __ p}
                                                       in
                                                       eq_rect_r l2' _evar_0_
                                                         (drop O l2')}
                                           in
                                           eq_rect_r O _evar_0_
                                             (subn (size0 l) (size0 l)))}
                             in
                             eq_rect_r False _evar_0_
                               (leq (S (size0 l)) (size0 l)))}
               in
               eq_rect_r
                 (case leq (S (size0 l)) (size0 l) of {
                   True -> cat (drop (size0 l) l) l2';
                   False -> drop (subn (size0 l) (size0 l)) l2'}) _evar_0_
                 (drop (size0 l) (cat l l2'))) l2) l'}
        in
        case __top_assumption_1 of {
         Pair _ x -> _evar_0_ x}}
      in
      case __top_assumption_0 of {
       ExistT x x0 -> _evar_0_ x x0}}
    in
    case __top_assumption_ of {
     Pair _ x -> unsafeCoerce _evar_0_ x}) (\l1 l2 __top_assumption_ ->
    let {
     _evar_0_ = \p -> ExistT l1 (ExistT (cat l l2) (Pair __ (ExistT l2 (Pair
      __ p))))}
    in
    case __top_assumption_ of {
     Pair _ x -> _evar_0_ x})
    (list_split_pickableT2 (\l1 l2 ->
      pickable_decidable_T
        (list_search_prefix_pickableT c (\l0 -> d l1 l0) l l2)) l')

list_split_pickable3_gen :: (List a1) -> ((List a1) -> (List a1) -> (List 
                            a1) -> () -> DecidableT a2) -> PickableT3
                            (List a1) (List a1) (List a1) (Prod () a2)
list_split_pickable3_gen l d =
  ssr_have (\l23 l1 _ ->
    unsafeCoerce list_split_pickableT2_gen l23 (\_l1_ _l2_ _ ->
      eq_rect_r (cat l1 l23) (\d0 ->
        eq_rect_r (cat _l1_ _l2_) (\d1 -> d1 l1 _l1_ _l2_ __) l23 d0) l d))
    (\d1 ->
    ssr_have
      (unsafeCoerce list_split_pickableT2_gen l (\l1 l23 _ ->
        let {d1' = d1 l23 l1 __} in
        let {d1'0 = pickable2_weaken_T (unsafeCoerce d1')} in
        pickable_decidable_T d1'0)) (\__top_assumption_ ->
      let {
       _evar_0_ = \__top_assumption_0 ->
        let {
         _evar_0_ = \__top_assumption_1 ->
          let {
           _evar_0_ = \l1 l23 __top_assumption_2 ->
            let {
             _evar_0_ = \h -> Inl
              (case d1 l23 l1 __ of {
                Inl __top_assumption_3 ->
                 let {
                  _evar_0_ = \__top_assumption_4 ->
                   let {
                    _evar_0_ = \l2 l3 __top_assumption_5 ->
                     let {
                      _evar_0_ = \p -> ExistT (Pair (Pair l1 l2) l3)
                       (eq_rect_r (cat l1 l23) (\d0 d2 ->
                         eq_rect_r (cat l2 l3) (\_ _ _ -> Pair __ p) l23 d2
                           d0 h) l d d1)}
                     in
                     case __top_assumption_5 of {
                      Pair _ x -> _evar_0_ x}}
                   in
                   case __top_assumption_4 of {
                    Pair x x0 -> _evar_0_ x x0}}
                 in
                 case __top_assumption_3 of {
                  ExistT x x0 -> _evar_0_ x x0};
                Inr _ -> false_rect})}
            in
            case __top_assumption_2 of {
             Pair _ x -> _evar_0_ x}}
          in
          case __top_assumption_1 of {
           Pair x x0 -> _evar_0_ x x0}}
        in
        case __top_assumption_0 of {
         ExistT x x0 -> _evar_0_ x x0}}
      in
      let {
       _evar_0_0 = \ex -> Inr (\__top_assumption_0 ->
        let {
         _evar_0_0 = \l1 __top_assumption_1 ->
          let {
           _evar_0_0 = \l2 __top_assumption_2 ->
            let {
             _evar_0_0 = \l3 __top_assumption_3 ->
              let {
               _evar_0_0 = \p ->
                ex (ExistT l1 (ExistT (cat l2 l3) (Pair __ (ExistT l2 (ExistT
                  l3 (Pair __ p))))))}
              in
              case __top_assumption_3 of {
               Pair _ x -> _evar_0_0 x}}
            in
            case __top_assumption_2 of {
             ExistT x x0 -> _evar_0_0 x x0}}
          in
          case __top_assumption_1 of {
           ExistT x x0 -> _evar_0_0 x x0}}
        in
        case __top_assumption_0 of {
         ExistT x x0 -> _evar_0_0 x x0})}
      in
      case __top_assumption_ of {
       Inl x -> unsafeCoerce _evar_0_ x;
       Inr x -> _evar_0_0 x}))

beq_dec :: Z -> Z -> Binary_float -> Binary_float -> Sumbool
beq_dec _ _ f1 f2 =
  case f1 of {
   B754_zero s1 ->
    case f2 of {
     B754_zero s2 ->
      case s1 of {
       True -> case s2 of {
                True -> Left;
                False -> Right};
       False -> case s2 of {
                 True -> Right;
                 False -> Left}};
     _ -> Right};
   B754_infinity s1 ->
    case f2 of {
     B754_infinity s2 ->
      case s1 of {
       True -> case s2 of {
                True -> Left;
                False -> Right};
       False -> case s2 of {
                 True -> Right;
                 False -> Left}};
     _ -> Right};
   B754_nan s1 p1 ->
    case f2 of {
     B754_nan s2 p2 ->
      case s1 of {
       True ->
        case s2 of {
         True ->
          let {s = eq_dec p1 p2} in
          case s of {
           Left -> eq_rec_r p2 (\_ -> Left) p1 __;
           Right -> Right};
         False -> Right};
       False ->
        case s2 of {
         True -> Right;
         False ->
          let {s = eq_dec p1 p2} in
          case s of {
           Left -> eq_rec_r p2 (\_ -> Left) p1 __;
           Right -> Right}}};
     _ -> Right};
   B754_finite s1 m1 e1 ->
    case f2 of {
     B754_finite s2 m2 e2 ->
      case s1 of {
       True ->
        case s2 of {
         True ->
          let {s = eq_dec m1 m2} in
          case s of {
           Left ->
            let {s0 = eq_dec0 e1 e2} in
            case s0 of {
             Left -> eq_rec_r m2 (\_ -> eq_rec_r e2 (\_ -> Left) e1 __) m1 __;
             Right -> Right};
           Right -> Right};
         False -> Right};
       False ->
        case s2 of {
         True -> Right;
         False ->
          let {s = eq_dec m1 m2} in
          case s of {
           Left ->
            let {s0 = eq_dec0 e1 e2} in
            case s0 of {
             Left -> eq_rec_r m2 (\_ -> eq_rec_r e2 (\_ -> Left) e1 __) m1 __;
             Right -> Right};
           Right -> Right}}};
     _ -> Right}}

bofZ :: Z -> Z -> Z -> Binary_float
bofZ prec1 emax1 n =
  binary_normalize prec1 emax1 Mode_NE n Z0 False

bconv :: Z -> Z -> Z -> Z -> (Binary_float -> Binary_float) -> Mode ->
         Binary_float -> Binary_float
bconv _ _ prec2 emax2 conv_nan md f =
  case f of {
   B754_nan _ _ -> build_nan prec2 emax2 (conv_nan f);
   B754_finite s m e ->
    binary_normalize prec2 emax2 md (cond_Zopp s (Zpos m)) e s;
   x -> x}

type Float = Binary64

type Float32 = Binary32

cmp_of_comparison :: Comparison0 -> (Option Comparison) -> Bool
cmp_of_comparison c x =
  case c of {
   Ceq ->
    case x of {
     Some c0 -> case c0 of {
                 Eq -> True;
                 _ -> False};
     None -> False};
   Cne ->
    case x of {
     Some c0 -> case c0 of {
                 Eq -> False;
                 _ -> True};
     None -> True};
   Clt ->
    case x of {
     Some c0 -> case c0 of {
                 Lt -> True;
                 _ -> False};
     None -> False};
   Cle ->
    case x of {
     Some c0 -> case c0 of {
                 Gt -> False;
                 _ -> True};
     None -> False};
   Cgt ->
    case x of {
     Some c0 -> case c0 of {
                 Gt -> True;
                 _ -> False};
     None -> False};
   Cge ->
    case x of {
     Some c0 -> case c0 of {
                 Lt -> False;
                 _ -> True};
     None -> False}}

quiet_nan_64_payload :: Positive -> Positive
quiet_nan_64_payload p =
  to_pos
    (p_mod_two_p
      (lor p
        (iter_nat (\x -> XO x) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))) XH)) (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))

quiet_nan_64 :: (Prod Bool Positive) -> Float
quiet_nan_64 sp =
  case sp of {
   Pair s p -> B754_nan s (quiet_nan_64_payload p)}

quiet_nan_32_payload :: Positive -> Positive
quiet_nan_32_payload p =
  to_pos
    (p_mod_two_p
      (lor p
        (iter_nat (\x -> XO x) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S O)))))))))))))))))))))) XH)) (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))

quiet_nan_32 :: (Prod Bool Positive) -> Float32
quiet_nan_32 sp =
  case sp of {
   Pair s p -> B754_nan s (quiet_nan_32_payload p)}

of_bits :: Int1 -> Float
of_bits b =
  b64_of_bits (unsigned1 b)

of_bits0 :: Int -> Float32
of_bits0 b =
  b32_of_bits (unsigned b)

data Mixin_of0 int_t =
   Mixin0 int_t (int_t -> int_t) (int_t -> int_t) (int_t -> int_t) (int_t ->
                                                                   int_t ->
                                                                   int_t) 
 (int_t -> int_t -> int_t) (int_t -> int_t -> int_t) (int_t -> int_t ->
                                                     Option int_t) (int_t ->
                                                                   int_t ->
                                                                   Option
                                                                   int_t) 
 (int_t -> int_t -> Option int_t) (int_t -> int_t -> Option int_t) (int_t ->
                                                                   int_t ->
                                                                   int_t) 
 (int_t -> int_t -> int_t) (int_t -> int_t -> int_t) (int_t -> int_t ->
                                                     int_t) (int_t -> int_t
                                                            -> int_t) 
 (int_t -> int_t -> int_t) (int_t -> int_t -> int_t) (int_t -> int_t ->
                                                     int_t) (int_t -> int_t
                                                            -> Bool) 
 (int_t -> Bool) (int_t -> int_t -> Bool) (int_t -> int_t -> Bool) (int_t ->
                                                                   int_t ->
                                                                   Bool) 
 (int_t -> int_t -> Bool) (int_t -> int_t -> Bool) (int_t -> int_t -> Bool) 
 (int_t -> int_t -> Bool) (int_t -> int_t -> Bool) (Z -> int_t) (int_t ->
                                                                Nat) 
 (int_t -> N) (int_t -> Z) (int_t -> Z)

int_zero :: (Mixin_of0 a1) -> a1
int_zero m =
  case m of {
   Mixin0 int_zero0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_zero0}

int_clz :: (Mixin_of0 a1) -> a1 -> a1
int_clz m =
  case m of {
   Mixin0 _ int_clz0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_clz0}

int_ctz :: (Mixin_of0 a1) -> a1 -> a1
int_ctz m =
  case m of {
   Mixin0 _ _ int_ctz0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_ctz0}

int_popcnt :: (Mixin_of0 a1) -> a1 -> a1
int_popcnt m =
  case m of {
   Mixin0 _ _ _ int_popcnt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ -> int_popcnt0}

int_add :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_add m =
  case m of {
   Mixin0 _ _ _ _ int_add0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_add0}

int_sub :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_sub m =
  case m of {
   Mixin0 _ _ _ _ _ int_sub0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_sub0}

int_mul :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_mul m =
  case m of {
   Mixin0 _ _ _ _ _ _ int_mul0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_mul0}

int_div_u :: (Mixin_of0 a1) -> a1 -> a1 -> Option a1
int_div_u m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ int_div_u0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ -> int_div_u0}

int_div_s :: (Mixin_of0 a1) -> a1 -> a1 -> Option a1
int_div_s m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ int_div_s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ -> int_div_s0}

int_rem_u :: (Mixin_of0 a1) -> a1 -> a1 -> Option a1
int_rem_u m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ int_rem_u0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ -> int_rem_u0}

int_rem_s :: (Mixin_of0 a1) -> a1 -> a1 -> Option a1
int_rem_s m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ int_rem_s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ -> int_rem_s0}

int_and :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_and m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ int_and0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_and0}

int_or :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_or m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ int_or0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ -> int_or0}

int_xor :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_xor m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ int_xor0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_xor0}

int_shl :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_shl m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_shl0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_shl0}

int_shr_u :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_shr_u m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_shr_u0 _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ -> int_shr_u0}

int_shr_s :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_shr_s m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_shr_s0 _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ -> int_shr_s0}

int_rotl :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_rotl m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_rotl0 _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_rotl0}

int_rotr :: (Mixin_of0 a1) -> a1 -> a1 -> a1
int_rotr m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_rotr0 _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_rotr0}

int_eq :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_eq m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_eq0 _ _ _ _ _ _ _ _ _ _ _
    _ _ _ -> int_eq0}

int_eqz :: (Mixin_of0 a1) -> a1 -> Bool
int_eqz m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_eqz0 _ _ _ _ _ _ _ _ _
    _ _ _ _ -> int_eqz0}

int_lt_u :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_lt_u m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_lt_u0 _ _ _ _ _ _ _ _
    _ _ _ _ -> int_lt_u0}

int_lt_s :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_lt_s m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_lt_s0 _ _ _ _ _ _ _
    _ _ _ _ -> int_lt_s0}

int_gt_u :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_gt_u m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_gt_u0 _ _ _ _ _ _
    _ _ _ _ -> int_gt_u0}

int_gt_s :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_gt_s m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_gt_s0 _ _ _ _ _
    _ _ _ _ -> int_gt_s0}

int_le_u :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_le_u m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_le_u0 _ _ _ _
    _ _ _ _ -> int_le_u0}

int_le_s :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_le_s m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_le_s0 _ _ _
    _ _ _ _ -> int_le_s0}

int_ge_u :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_ge_u m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_ge_u0 _ _
    _ _ _ _ -> int_ge_u0}

int_ge_s :: (Mixin_of0 a1) -> a1 -> a1 -> Bool
int_ge_s m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_ge_s0 _
    _ _ _ _ -> int_ge_s0}

int_of_Z :: (Mixin_of0 a1) -> Z -> a1
int_of_Z m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_of_Z0
    _ _ _ _ -> int_of_Z0}

nat_of_uint :: (Mixin_of0 a1) -> a1 -> Nat
nat_of_uint m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    nat_of_uint0 _ _ _ -> nat_of_uint0}

n_of_uint :: (Mixin_of0 a1) -> a1 -> N
n_of_uint m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    n_of_uint0 _ _ -> n_of_uint0}

z_of_uint :: (Mixin_of0 a1) -> a1 -> Z
z_of_uint m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    z_of_uint0 _ -> z_of_uint0}

z_of_sint :: (Mixin_of0 a1) -> a1 -> Z
z_of_sint m =
  case m of {
   Mixin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    z_of_sint0 -> z_of_sint0}

data Class_of t =
   Class (Mixin_of t) (Mixin_of0 t)

base :: (Class_of a1) -> Mixin_of a1
base c =
  case c of {
   Class base1 _ -> base1}

mixin :: (Class_of a1) -> Mixin_of0 a1
mixin c =
  case c of {
   Class _ mixin1 -> mixin1}

type Type0 = Class_of Any
  -- singleton inductive, whose constructor was Pack
  
type Sort0 = Any

int_ne :: Type0 -> Sort0 -> Sort0 -> Bool
int_ne e x y =
  case e of {
   Class _ m -> negb (int_eq m x y)}

wordsize5 :: Nat
wordsize5 =
  wordsize

zwordsize1 :: Z
zwordsize1 =
  of_nat1 wordsize5

modulus2 :: Z
modulus2 =
  two_power_nat wordsize5

half_modulus1 :: Z
half_modulus1 =
  div0 modulus2 (Zpos (XO XH))

max_unsigned1 :: Z
max_unsigned1 =
  sub2 modulus2 (Zpos XH)

max_signed1 :: Z
max_signed1 =
  sub2 half_modulus1 (Zpos XH)

min_signed1 :: Z
min_signed1 =
  opp half_modulus1

type Int2 = Z
  -- singleton inductive, whose constructor was mkint
  
intval2 :: Int2 -> Z
intval2 i =
  i

z_mod_modulus2 :: Z -> Z
z_mod_modulus2 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> p_mod_two_p p wordsize5;
   Zneg p ->
    let {r = p_mod_two_p p wordsize5} in
    case zeq r Z0 of {
     Left -> Z0;
     Right -> sub2 modulus2 r}}

unsigned2 :: Int2 -> Z
unsigned2 =
  intval2

signed1 :: Int2 -> Z
signed1 n =
  let {x = unsigned2 n} in
  case zlt x half_modulus1 of {
   Left -> x;
   Right -> sub2 x modulus2}

repr2 :: Z -> Int2
repr2 =
  z_mod_modulus2

zero1 :: Int2
zero1 =
  repr2 Z0

one1 :: Int2
one1 =
  repr2 (Zpos XH)

mone1 :: Int2
mone1 =
  repr2 (Zneg XH)

eq1 :: Int2 -> Int2 -> Bool
eq1 x y =
  case zeq (unsigned2 x) (unsigned2 y) of {
   Left -> True;
   Right -> False}

lt1 :: Int2 -> Int2 -> Bool
lt1 x y =
  case zlt (signed1 x) (signed1 y) of {
   Left -> True;
   Right -> False}

ltu1 :: Int2 -> Int2 -> Bool
ltu1 x y =
  case zlt (unsigned2 x) (unsigned2 y) of {
   Left -> True;
   Right -> False}

add7 :: Int2 -> Int2 -> Int2
add7 x y =
  repr2 (add3 (unsigned2 x) (unsigned2 y))

sub5 :: Int2 -> Int2 -> Int2
sub5 x y =
  repr2 (sub2 (unsigned2 x) (unsigned2 y))

mul4 :: Int2 -> Int2 -> Int2
mul4 x y =
  repr2 (mul1 (unsigned2 x) (unsigned2 y))

divu1 :: Int2 -> Int2 -> Int2
divu1 x y =
  repr2 (div0 (unsigned2 x) (unsigned2 y))

modu1 :: Int2 -> Int2 -> Int2
modu1 x y =
  repr2 (modulo (unsigned2 x) (unsigned2 y))

and1 :: Int2 -> Int2 -> Int2
and1 x y =
  repr2 (land1 (unsigned2 x) (unsigned2 y))

or1 :: Int2 -> Int2 -> Int2
or1 x y =
  repr2 (lor1 (unsigned2 x) (unsigned2 y))

xor1 :: Int2 -> Int2 -> Int2
xor1 x y =
  repr2 (lxor1 (unsigned2 x) (unsigned2 y))

shl1 :: Int2 -> Int2 -> Int2
shl1 x y =
  repr2 (shiftl (unsigned2 x) (unsigned2 y))

shru1 :: Int2 -> Int2 -> Int2
shru1 x y =
  repr2 (shiftr (unsigned2 x) (unsigned2 y))

shr2 :: Int2 -> Int2 -> Int2
shr2 x y =
  repr2 (shiftr (signed1 x) (unsigned2 y))

rol1 :: Int2 -> Int2 -> Int2
rol1 x y =
  let {n = modulo (unsigned2 y) zwordsize1} in
  repr2
    (lor1 (shiftl (unsigned2 x) n)
      (shiftr (unsigned2 x) (sub2 zwordsize1 n)))

ror1 :: Int2 -> Int2 -> Int2
ror1 x y =
  let {n = modulo (unsigned2 y) zwordsize1} in
  repr2
    (lor1 (shiftr (unsigned2 x) n)
      (shiftl (unsigned2 x) (sub2 zwordsize1 n)))

type T = Int2

eq_eqP :: Axiom T
eq_eqP x y =
  let {_evar_0_ = \_ -> ReflectT} in
  let {_evar_0_0 = \_ -> ReflectF} in
  case zeq (unsigned2 x) (unsigned2 y) of {
   Left -> _evar_0_ __;
   Right -> _evar_0_0 __}

power_index_to_bits :: Nat -> (List Z) -> List Bool
power_index_to_bits c l =
  case c of {
   O -> Nil;
   S c0 -> Cons
    (in_mem (unsafeCoerce of_nat1 c0)
      (mem (seq_predType z_eqType) (unsafeCoerce l)))
    (power_index_to_bits c0 l)}

convert_to_bits :: T -> List Bool
convert_to_bits x =
  power_index_to_bits wordsize5 (z_one_bits wordsize5 (intval2 x) Z0)

clz :: T -> Int2
clz i =
  repr2
    (of_nat1
      (find (\b -> eq_op bool_eqType (unsafeCoerce b) (unsafeCoerce True))
        (convert_to_bits i)))

ctz :: T -> Int2
ctz i =
  repr2
    (of_nat1
      (find (\b -> eq_op bool_eqType (unsafeCoerce b) (unsafeCoerce True))
        (rev0 (convert_to_bits i))))

popcnt :: T -> Int2
popcnt i =
  repr2
    (of_nat1
      (count (\b -> eq_op bool_eqType (unsafeCoerce b) (unsafeCoerce True))
        (convert_to_bits i)))

iadd :: T -> T -> T
iadd =
  add7

isub :: T -> T -> T
isub =
  sub5

imul :: T -> T -> T
imul =
  mul4

idiv_u :: T -> T -> Option T
idiv_u i1 i2 =
  case eq1 i2 zero1 of {
   True -> None;
   False -> Some (divu1 i1 i2)}

idiv_s :: T -> T -> Option T
idiv_s i1 i2 =
  case eq_op z_eqType (unsafeCoerce signed1 i2) (unsafeCoerce of_nat1 O) of {
   True -> None;
   False ->
    case eq_op z_eqType (unsafeCoerce quot (signed1 i1) (signed1 i2))
           (unsafeCoerce half_modulus1) of {
     True -> None;
     False -> Some (repr2 (quot (signed1 i1) (signed1 i2)))}}

irem_u :: T -> T -> Option T
irem_u i1 i2 =
  case eq1 i2 zero1 of {
   True -> None;
   False -> Some (modu1 i1 i2)}

irem_s :: T -> T -> Option T
irem_s i1 i2 =
  case eq_op z_eqType (unsafeCoerce signed1 i2) (unsafeCoerce of_nat1 O) of {
   True -> None;
   False -> Some
    (repr2
      (case eq_op z_eqType (unsafeCoerce modulo (signed1 i1) (signed1 i2))
              (unsafeCoerce of_nat1 O) of {
        True -> modulo (signed1 i1) (signed1 i2);
        False ->
         case geb (modulo (signed1 i1) (signed1 i2)) Z0 of {
          True ->
           case geb (signed1 i1) Z0 of {
            True -> modulo (signed1 i1) (signed1 i2);
            False -> sub2 (modulo (signed1 i1) (signed1 i2)) (signed1 i2)};
          False ->
           case geb (signed1 i1) Z0 of {
            True -> sub2 (modulo (signed1 i1) (signed1 i2)) (signed1 i2);
            False -> modulo (signed1 i1) (signed1 i2)}}}))}

iand :: T -> T -> T
iand =
  and1

ior :: T -> T -> T
ior =
  or1

ixor :: T -> T -> T
ixor =
  xor1

ishl :: T -> T -> T
ishl =
  shl1

ishr_u :: T -> T -> T
ishr_u =
  shru1

tmixin :: Mixin_of0 T
tmixin =
  Mixin0 zero1 clz ctz popcnt iadd isub imul idiv_u idiv_s irem_u irem_s iand
    ior ixor ishl ishr_u shr2 rol1 ror1 eq1 (eq1 zero1) ltu1 lt1 (\x y ->
    ltu1 y x) (\x y -> lt1 y x) (\x y -> negb (ltu1 y x)) (\x y ->
    negb (lt1 y x)) (\x y -> negb (ltu1 x y)) (\x y -> negb (lt1 x y)) repr2
    (\i -> to_nat1 (unsigned2 i)) (\i -> to_N (unsigned2 i)) unsigned2
    signed1

cT :: Type0
cT =
  Class (Mixin (unsafeCoerce eq1) (unsafeCoerce eq_eqP))
    (unsafeCoerce tmixin)

class1 :: Class_of Sort0
class1 =
  cT

eqType :: Type
eqType =
  base class1

wordsize6 :: Nat
wordsize6 =
  wordsize3

zwordsize2 :: Z
zwordsize2 =
  of_nat1 wordsize6

modulus3 :: Z
modulus3 =
  two_power_nat wordsize6

half_modulus2 :: Z
half_modulus2 =
  div0 modulus3 (Zpos (XO XH))

max_unsigned2 :: Z
max_unsigned2 =
  sub2 modulus3 (Zpos XH)

min_signed2 :: Z
min_signed2 =
  opp half_modulus2

type Int3 = Z
  -- singleton inductive, whose constructor was mkint
  
intval3 :: Int3 -> Z
intval3 i =
  i

z_mod_modulus3 :: Z -> Z
z_mod_modulus3 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> p_mod_two_p p wordsize6;
   Zneg p ->
    let {r = p_mod_two_p p wordsize6} in
    case zeq r Z0 of {
     Left -> Z0;
     Right -> sub2 modulus3 r}}

unsigned3 :: Int3 -> Z
unsigned3 =
  intval3

signed2 :: Int3 -> Z
signed2 n =
  let {x = unsigned3 n} in
  case zlt x half_modulus2 of {
   Left -> x;
   Right -> sub2 x modulus3}

repr3 :: Z -> Int3
repr3 =
  z_mod_modulus3

zero2 :: Int3
zero2 =
  repr3 Z0

eq2 :: Int3 -> Int3 -> Bool
eq2 x y =
  case zeq (unsigned3 x) (unsigned3 y) of {
   Left -> True;
   Right -> False}

lt2 :: Int3 -> Int3 -> Bool
lt2 x y =
  case zlt (signed2 x) (signed2 y) of {
   Left -> True;
   Right -> False}

ltu2 :: Int3 -> Int3 -> Bool
ltu2 x y =
  case zlt (unsigned3 x) (unsigned3 y) of {
   Left -> True;
   Right -> False}

add8 :: Int3 -> Int3 -> Int3
add8 x y =
  repr3 (add3 (unsigned3 x) (unsigned3 y))

sub6 :: Int3 -> Int3 -> Int3
sub6 x y =
  repr3 (sub2 (unsigned3 x) (unsigned3 y))

mul5 :: Int3 -> Int3 -> Int3
mul5 x y =
  repr3 (mul1 (unsigned3 x) (unsigned3 y))

divu2 :: Int3 -> Int3 -> Int3
divu2 x y =
  repr3 (div0 (unsigned3 x) (unsigned3 y))

modu2 :: Int3 -> Int3 -> Int3
modu2 x y =
  repr3 (modulo (unsigned3 x) (unsigned3 y))

and2 :: Int3 -> Int3 -> Int3
and2 x y =
  repr3 (land1 (unsigned3 x) (unsigned3 y))

or2 :: Int3 -> Int3 -> Int3
or2 x y =
  repr3 (lor1 (unsigned3 x) (unsigned3 y))

xor2 :: Int3 -> Int3 -> Int3
xor2 x y =
  repr3 (lxor1 (unsigned3 x) (unsigned3 y))

shl2 :: Int3 -> Int3 -> Int3
shl2 x y =
  repr3 (shiftl (unsigned3 x) (unsigned3 y))

shru2 :: Int3 -> Int3 -> Int3
shru2 x y =
  repr3 (shiftr (unsigned3 x) (unsigned3 y))

shr3 :: Int3 -> Int3 -> Int3
shr3 x y =
  repr3 (shiftr (signed2 x) (unsigned3 y))

rol2 :: Int3 -> Int3 -> Int3
rol2 x y =
  let {n = modulo (unsigned3 y) zwordsize2} in
  repr3
    (lor1 (shiftl (unsigned3 x) n)
      (shiftr (unsigned3 x) (sub2 zwordsize2 n)))

ror2 :: Int3 -> Int3 -> Int3
ror2 x y =
  let {n = modulo (unsigned3 y) zwordsize2} in
  repr3
    (lor1 (shiftr (unsigned3 x) n)
      (shiftl (unsigned3 x) (sub2 zwordsize2 n)))

type T0 = Int3

eq_eqP0 :: Axiom T0
eq_eqP0 x y =
  let {_evar_0_ = \_ -> ReflectT} in
  let {_evar_0_0 = \_ -> ReflectF} in
  case zeq (unsigned3 x) (unsigned3 y) of {
   Left -> _evar_0_ __;
   Right -> _evar_0_0 __}

power_index_to_bits0 :: Nat -> (List Z) -> List Bool
power_index_to_bits0 c l =
  case c of {
   O -> Nil;
   S c0 -> Cons
    (in_mem (unsafeCoerce of_nat1 c0)
      (mem (seq_predType z_eqType) (unsafeCoerce l)))
    (power_index_to_bits0 c0 l)}

convert_to_bits0 :: T0 -> List Bool
convert_to_bits0 x =
  power_index_to_bits0 wordsize6 (z_one_bits wordsize6 (intval3 x) Z0)

clz0 :: T0 -> Int3
clz0 i =
  repr3
    (of_nat1
      (find (\b -> eq_op bool_eqType (unsafeCoerce b) (unsafeCoerce True))
        (convert_to_bits0 i)))

ctz0 :: T0 -> Int3
ctz0 i =
  repr3
    (of_nat1
      (find (\b -> eq_op bool_eqType (unsafeCoerce b) (unsafeCoerce True))
        (rev0 (convert_to_bits0 i))))

popcnt0 :: T0 -> Int3
popcnt0 i =
  repr3
    (of_nat1
      (count (\b -> eq_op bool_eqType (unsafeCoerce b) (unsafeCoerce True))
        (convert_to_bits0 i)))

iadd0 :: T0 -> T0 -> T0
iadd0 =
  add8

isub0 :: T0 -> T0 -> T0
isub0 =
  sub6

imul0 :: T0 -> T0 -> T0
imul0 =
  mul5

idiv_u0 :: T0 -> T0 -> Option T0
idiv_u0 i1 i2 =
  case eq2 i2 zero2 of {
   True -> None;
   False -> Some (divu2 i1 i2)}

idiv_s0 :: T0 -> T0 -> Option T0
idiv_s0 i1 i2 =
  case eq_op z_eqType (unsafeCoerce signed2 i2) (unsafeCoerce of_nat1 O) of {
   True -> None;
   False ->
    case eq_op z_eqType (unsafeCoerce quot (signed2 i1) (signed2 i2))
           (unsafeCoerce half_modulus2) of {
     True -> None;
     False -> Some (repr3 (quot (signed2 i1) (signed2 i2)))}}

irem_u0 :: T0 -> T0 -> Option T0
irem_u0 i1 i2 =
  case eq2 i2 zero2 of {
   True -> None;
   False -> Some (modu2 i1 i2)}

irem_s0 :: T0 -> T0 -> Option T0
irem_s0 i1 i2 =
  case eq_op z_eqType (unsafeCoerce signed2 i2) (unsafeCoerce of_nat1 O) of {
   True -> None;
   False -> Some
    (repr3
      (case eq_op z_eqType (unsafeCoerce modulo (signed2 i1) (signed2 i2))
              (unsafeCoerce of_nat1 O) of {
        True -> modulo (signed2 i1) (signed2 i2);
        False ->
         case geb (modulo (signed2 i1) (signed2 i2)) Z0 of {
          True ->
           case geb (signed2 i1) Z0 of {
            True -> modulo (signed2 i1) (signed2 i2);
            False -> sub2 (modulo (signed2 i1) (signed2 i2)) (signed2 i2)};
          False ->
           case geb (signed2 i1) Z0 of {
            True -> sub2 (modulo (signed2 i1) (signed2 i2)) (signed2 i2);
            False -> modulo (signed2 i1) (signed2 i2)}}}))}

iand0 :: T0 -> T0 -> T0
iand0 =
  and2

ior0 :: T0 -> T0 -> T0
ior0 =
  or2

ixor0 :: T0 -> T0 -> T0
ixor0 =
  xor2

ishl0 :: T0 -> T0 -> T0
ishl0 =
  shl2

ishr_u0 :: T0 -> T0 -> T0
ishr_u0 =
  shru2

tmixin0 :: Mixin_of0 T0
tmixin0 =
  Mixin0 zero2 clz0 ctz0 popcnt0 iadd0 isub0 imul0 idiv_u0 idiv_s0 irem_u0
    irem_s0 iand0 ior0 ixor0 ishl0 ishr_u0 shr3 rol2 ror2 eq2 (eq2 zero2)
    ltu2 lt2 (\x y -> ltu2 y x) (\x y -> lt2 y x) (\x y -> negb (ltu2 y x))
    (\x y -> negb (lt2 y x)) (\x y -> negb (ltu2 x y)) (\x y ->
    negb (lt2 x y)) repr3 (\i -> to_nat1 (unsigned3 i)) (\i ->
    to_N (unsigned3 i)) unsigned3 signed2

cT0 :: Type0
cT0 =
  Class (Mixin (unsafeCoerce eq2) (unsafeCoerce eq_eqP0))
    (unsafeCoerce tmixin0)

class2 :: Class_of Sort0
class2 =
  cT0

eqType0 :: Type
eqType0 =
  base class2

i32 :: Type
i32 =
  eqType

i32r :: Class_of Sort
i32r =
  class1

i32t :: Type0
i32t =
  i32r

i32m :: Mixin_of0 Sort
i32m =
  mixin i32r

i64 :: Type
i64 =
  eqType0

i64r :: Class_of Sort
i64r =
  class2

i64t :: Type0
i64t =
  i64r

i64m :: Mixin_of0 Sort
i64m =
  mixin i64r

wasm_wrap :: Sort -> Sort
wasm_wrap i =
  int_of_Z i32m (z_of_uint i64m i)

wasm_extend_u :: Sort -> Sort
wasm_extend_u i =
  int_of_Z i64m (z_of_uint i32m i)

wasm_extend_s :: Sort -> Sort
wasm_extend_s i =
  int_of_Z i64m (z_of_sint i32m i)

data Mixin_of1 float_t =
   Mixin1 float_t (float_t -> float_t) (float_t -> float_t) (float_t ->
                                                            float_t) 
 (float_t -> float_t) (float_t -> float_t) (float_t -> float_t) (float_t ->
                                                                float_t) 
 (float_t -> float_t -> float_t) (float_t -> float_t -> float_t) (float_t ->
                                                                 float_t ->
                                                                 float_t) 
 (float_t -> float_t -> float_t) (float_t -> float_t -> float_t) (float_t ->
                                                                 float_t ->
                                                                 float_t) 
 (float_t -> float_t -> float_t) (float_t -> float_t -> Bool) (float_t ->
                                                              float_t ->
                                                              Bool) (float_t
                                                                    ->
                                                                    float_t
                                                                    -> Bool) 
 (float_t -> float_t -> Bool) (float_t -> float_t -> Bool) (float_t -> Option
                                                           Sort) (float_t ->
                                                                 Option 
                                                                 Sort) 
 (float_t -> Option Sort) (float_t -> Option Sort) (Sort -> float_t) 
 (Sort -> float_t) (Sort -> float_t) (Sort -> float_t)

float_zero :: (Mixin_of1 a1) -> a1
float_zero m =
  case m of {
   Mixin1 float_zero0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ -> float_zero0}

float_neg :: (Mixin_of1 a1) -> a1 -> a1
float_neg m =
  case m of {
   Mixin1 _ float_neg0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_neg0}

float_abs :: (Mixin_of1 a1) -> a1 -> a1
float_abs m =
  case m of {
   Mixin1 _ _ float_abs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_abs0}

float_sqrt :: (Mixin_of1 a1) -> a1 -> a1
float_sqrt m =
  case m of {
   Mixin1 _ _ _ float_sqrt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ -> float_sqrt0}

float_ceil :: (Mixin_of1 a1) -> a1 -> a1
float_ceil m =
  case m of {
   Mixin1 _ _ _ _ float_ceil0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ -> float_ceil0}

float_floor :: (Mixin_of1 a1) -> a1 -> a1
float_floor m =
  case m of {
   Mixin1 _ _ _ _ _ float_floor0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ -> float_floor0}

float_trunc :: (Mixin_of1 a1) -> a1 -> a1
float_trunc m =
  case m of {
   Mixin1 _ _ _ _ _ _ float_trunc0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ -> float_trunc0}

float_nearest :: (Mixin_of1 a1) -> a1 -> a1
float_nearest m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ float_nearest0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ -> float_nearest0}

float_add :: (Mixin_of1 a1) -> a1 -> a1 -> a1
float_add m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ float_add0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_add0}

float_sub :: (Mixin_of1 a1) -> a1 -> a1 -> a1
float_sub m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ float_sub0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_sub0}

float_mul :: (Mixin_of1 a1) -> a1 -> a1 -> a1
float_mul m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ float_mul0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_mul0}

float_div :: (Mixin_of1 a1) -> a1 -> a1 -> a1
float_div m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ float_div0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_div0}

float_min :: (Mixin_of1 a1) -> a1 -> a1 -> a1
float_min m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ float_min0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_min0}

float_max :: (Mixin_of1 a1) -> a1 -> a1 -> a1
float_max m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ float_max0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_max0}

float_copysign :: (Mixin_of1 a1) -> a1 -> a1 -> a1
float_copysign m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_copysign0 _ _ _ _ _ _ _ _ _ _ _ _
    _ -> float_copysign0}

float_eq :: (Mixin_of1 a1) -> a1 -> a1 -> Bool
float_eq m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_eq0 _ _ _ _ _ _ _ _ _ _ _ _ ->
    float_eq0}

float_lt :: (Mixin_of1 a1) -> a1 -> a1 -> Bool
float_lt m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_lt0 _ _ _ _ _ _ _ _ _ _ _ ->
    float_lt0}

float_gt :: (Mixin_of1 a1) -> a1 -> a1 -> Bool
float_gt m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_gt0 _ _ _ _ _ _ _ _ _ _ ->
    float_gt0}

float_le :: (Mixin_of1 a1) -> a1 -> a1 -> Bool
float_le m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_le0 _ _ _ _ _ _ _ _ _ ->
    float_le0}

float_ge :: (Mixin_of1 a1) -> a1 -> a1 -> Bool
float_ge m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_ge0 _ _ _ _ _ _ _ _ ->
    float_ge0}

float_ui32_trunc :: (Mixin_of1 a1) -> a1 -> Option Sort
float_ui32_trunc m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_ui32_trunc0 _ _ _ _ _
    _ _ -> float_ui32_trunc0}

float_ui64_trunc :: (Mixin_of1 a1) -> a1 -> Option Sort
float_ui64_trunc m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_ui64_trunc0 _ _ _
    _ _ -> float_ui64_trunc0}

float_si64_trunc :: (Mixin_of1 a1) -> a1 -> Option Sort
float_si64_trunc m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_si64_trunc0 _ _
    _ _ -> float_si64_trunc0}

float_convert_ui32 :: (Mixin_of1 a1) -> Sort -> a1
float_convert_ui32 m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_convert_ui33
    _ _ _ -> float_convert_ui33}

float_convert_si32 :: (Mixin_of1 a1) -> Sort -> a1
float_convert_si32 m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    float_convert_si33 _ _ -> float_convert_si33}

float_convert_ui64 :: (Mixin_of1 a1) -> Sort -> a1
float_convert_ui64 m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    float_convert_ui65 _ -> float_convert_ui65}

float_convert_si64 :: (Mixin_of1 a1) -> Sort -> a1
float_convert_si64 m =
  case m of {
   Mixin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    float_convert_si65 -> float_convert_si65}

data Class_of0 t =
   Class0 (Mixin_of t) (Mixin_of1 t)

base0 :: (Class_of0 a1) -> Mixin_of a1
base0 c =
  case c of {
   Class0 base1 _ -> base1}

mixin0 :: (Class_of0 a1) -> Mixin_of1 a1
mixin0 c =
  case c of {
   Class0 _ mixin1 -> mixin1}

type Type1 = Class_of0 Any
  -- singleton inductive, whose constructor was Pack
  
type Sort1 = Any

float_ne :: Type1 -> Sort1 -> Sort1 -> Bool
float_ne e x y =
  case e of {
   Class0 _ m -> negb (float_eq m x y)}

cons_pl :: Float32 -> (List (Prod Bool Positive)) -> List
           (Prod Bool Positive)
cons_pl x l =
  case x of {
   B754_nan s p -> Cons (Pair s p) l;
   _ -> l}

binop_nan :: Float32 -> Float32 -> Float32
binop_nan x y =
  quiet_nan_32 (choose_nan_32 (cons_pl x (cons_pl y Nil)))

eq_dec3 :: Float32 -> Float32 -> Sumbool
eq_dec3 =
  beq_dec (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    XH))))))))

add9 :: Float32 -> Float32 -> Float32
add9 =
  bplus (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))) binop_nan Mode_NE

sub7 :: Float32 -> Float32 -> Float32
sub7 =
  bminus (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))) binop_nan Mode_NE

mul6 :: Float32 -> Float32 -> Float32
mul6 =
  bmult (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))) binop_nan Mode_NE

div3 :: Float32 -> Float32 -> Float32
div3 =
  bdiv (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))) binop_nan Mode_NE

compare2 :: Float32 -> Float32 -> Option Comparison
compare2 f1 f2 =
  bcompare (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))) f1 f2

cmp1 :: Comparison0 -> Float32 -> Float32 -> Bool
cmp1 c f1 f2 =
  cmp_of_comparison c (compare2 f1 f2)

to_bits :: Float32 -> Int
to_bits f =
  repr (bits_of_b32 f)

prec :: Z
prec =
  Zpos (XO (XO (XO (XI XH))))

emax :: Z
emax =
  Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))

type T1 = Float32

default_nan :: Binary32
default_nan =
  default_nan_pl32

cons_pl0 :: Float -> (List (Prod Bool Positive)) -> List (Prod Bool Positive)
cons_pl0 x l =
  case x of {
   B754_nan s p -> Cons (Pair s p) l;
   _ -> l}

binop_nan0 :: Float -> Float -> Float
binop_nan0 x y =
  quiet_nan_64 (choose_nan_64 (cons_pl0 x (cons_pl0 y Nil)))

eq_dec4 :: Float -> Float -> Sumbool
eq_dec4 =
  beq_dec (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XO XH)))))))))))

add10 :: Float -> Float -> Float
add10 =
  bplus (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO XH))))))))))) binop_nan0 Mode_NE

sub8 :: Float -> Float -> Float
sub8 =
  bminus (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO XH))))))))))) binop_nan0 Mode_NE

mul7 :: Float -> Float -> Float
mul7 =
  bmult (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO XH))))))))))) binop_nan0 Mode_NE

div4 :: Float -> Float -> Float
div4 =
  bdiv (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO XH))))))))))) binop_nan0 Mode_NE

compare3 :: Float -> Float -> Option Comparison
compare3 f1 f2 =
  bcompare (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XO XH))))))))))) f1 f2

cmp2 :: Comparison0 -> Float -> Float -> Bool
cmp2 c f1 f2 =
  cmp_of_comparison c (compare3 f1 f2)

to_bits0 :: Float -> Int1
to_bits0 f =
  repr1 (bits_of_b64 f)

prec0 :: Z
prec0 =
  Zpos (XI (XO (XI (XO (XI XH)))))

emax0 :: Z
emax0 =
  Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))

type T2 = Float

default_nan0 :: Binary64
default_nan0 =
  default_nan_pl64

eqb4 :: Binary_float -> Binary_float -> Bool
eqb4 v1 v2 =
  is_left (eq_dec3 v1 v2)

eqbP0 :: Axiom Binary_float
eqbP0 =
  eq_dec_Equality_axiom eq_dec3

t_eqMixin :: Mixin_of Binary_float
t_eqMixin =
  Mixin eqb4 eqbP0

t_eqType :: Type
t_eqType =
  unsafeCoerce t_eqMixin

is_nan0 :: T1 -> Bool
is_nan0 =
  is_nan prec emax

sign :: T1 -> Bool
sign =
  bsign prec emax

is_zero :: T1 -> Bool
is_zero z =
  case z of {
   B754_zero _ -> True;
   _ -> False}

is_infinity :: T1 -> Bool
is_infinity z =
  case z of {
   B754_infinity _ -> True;
   _ -> False}

pos_infinity :: T1
pos_infinity =
  B754_infinity False

neg_infinity :: T1
neg_infinity =
  B754_infinity True

pos_zero :: T1
pos_zero =
  B754_zero False

neg_zero :: T1
neg_zero =
  B754_zero True

canonical_pl :: Positive
canonical_pl =
  shift_pos (sub0 (to_pos prec) (XO XH)) XH

is_canonical :: T1 -> Bool
is_canonical z =
  case z of {
   B754_nan _ pl ->
    eq_op pos_eqType (unsafeCoerce pl) (unsafeCoerce canonical_pl);
   _ -> False}

pl_arithmetic :: Positive -> Bool
pl_arithmetic pl =
  eq_op z_eqType (unsafeCoerce (Zpos (digits2_pos pl)))
    (unsafeCoerce sub2 prec (Zpos XH))

canonical_nan :: Bool -> T1
canonical_nan s =
  B754_nan s canonical_pl

unspec_canonical_nan :: T1
unspec_canonical_nan =
  canonical_nan False

make_arithmetic :: Positive -> Positive
make_arithmetic __top_assumption_ =
  let {_evar_0_ = \_ -> __top_assumption_} in
  let {
   _evar_0_0 = \_ ->
    let {_evar_0_0 = \_ _ -> false_rec} in
    let {_evar_0_1 = \_ -> lor __top_assumption_ canonical_pl} in
    let {_evar_0_2 = \_ -> false_rec} in
    case prec of {
     Z0 -> _evar_0_0 __ __;
     Zpos x -> _evar_0_1 x;
     Zneg x -> _evar_0_2 x}}
  in
  case pl_arithmetic __top_assumption_ of {
   True -> _evar_0_ __;
   False -> _evar_0_0 __}

unspec_nan_pl :: Positive
unspec_nan_pl =
  ssr_have
    (let {_evar_0_ = \_ -> false_rec} in
     let {_evar_0_0 = \_ -> false_rec} in
     let {_evar_0_1 = \_ pl -> pl} in
     let {_evar_0_2 = \_ _ _ -> false_rec} in
     case default_nan of {
      B754_zero x -> _evar_0_ x;
      B754_infinity x -> _evar_0_0 x;
      B754_nan x x0 -> _evar_0_1 x x0;
      B754_finite x x0 x1 -> _evar_0_2 x x0 x1}) (\pl -> pl)

unspec_arithmetic_nan_pl :: Positive
unspec_arithmetic_nan_pl =
  make_arithmetic unspec_nan_pl

unspec_arithmetic_nan :: T1
unspec_arithmetic_nan =
  B754_nan True (proj1_sig unspec_arithmetic_nan_pl)

unspec_nan_nan :: T1
unspec_nan_nan =
  unspec_arithmetic_nan

unspec_nan :: T1
unspec_nan =
  proj1_sig unspec_nan_nan

opp0 :: T1 -> T1
opp0 =
  bopp prec emax (\_ -> unspec_nan)

normalise :: Z -> Z -> T1
normalise m e =
  binary_normalize prec emax Mode_NE m e False

nans :: (List T1) -> T1
nans zs =
  case all is_canonical (filter is_nan0 zs) of {
   True -> unspec_canonical_nan;
   False -> unspec_arithmetic_nan}

sqrt :: T1 -> T1
sqrt z =
  bsqrt prec emax (\z0 -> nans (Cons z0 Nil)) Mode_NE z

zofB_param :: (Z -> Z -> Z) -> (Z -> Z -> Z) -> T1 -> Option Z
zofB_param divP divN z =
  case z of {
   B754_zero _ -> Some Z0;
   B754_finite s m e0 ->
    case e0 of {
     Z0 -> Some (cond_Zopp s (Zpos m));
     Zpos e -> Some
      (mul1 (cond_Zopp s (Zpos m)) (pow_pos (radix_val radix2) e));
     Zneg e -> Some
      (cond_Zopp s
        (case s of {
          True -> divN (Zpos m) (pow_pos (radix_val radix2) e);
          False -> divP (Zpos m) (pow_pos (radix_val radix2) e)}))};
   _ -> None}

div_down :: Z -> Z -> Z
div_down =
  div0

div_up :: Z -> Z -> Z
div_up a b =
  add3 (case zeq_bool (modulo a b) Z0 of {
         True -> Z0;
         False -> Zpos XH}) (div0 a b)

div_near :: Z -> Z -> Z
div_near a b =
  case ltb0 (modulo a b) (div0 b (Zpos (XO XH))) of {
   True -> div_down a b;
   False ->
    case gtb (modulo a b) (div0 b (Zpos (XO XH))) of {
     True -> div_up a b;
     False ->
      case even (div_down a b) of {
       True -> div_down a b;
       False -> div_up a b}}}

ceilo :: T1 -> Option Z
ceilo =
  zofB_param div_up div_down

flooro :: T1 -> Option Z
flooro =
  zofB_param div_down div_up

trunco :: T1 -> Option Z
trunco =
  zofB_param div_down div_down

nearesto :: T1 -> Option Z
nearesto =
  zofB_param div_near div_near

bofZ0 :: Z -> T1
bofZ0 =
  bofZ prec emax

floatify :: (T1 -> Option Z) -> T1 -> T1
floatify f z =
  case f z of {
   Some i -> bofZ0 i;
   None -> z}

ceil :: T1 -> T1
ceil =
  floatify ceilo

floor :: T1 -> T1
floor =
  floatify flooro

trunc :: T1 -> T1
trunc =
  floatify trunco

nearest :: T1 -> T1
nearest =
  floatify nearesto

set_sign :: Bool -> T1 -> T1
set_sign s z =
  case z of {
   B754_zero _ -> B754_zero s;
   B754_infinity _ -> B754_infinity s;
   B754_nan _ pl -> B754_nan s pl;
   B754_finite _ m e -> B754_finite s m e}

fadd :: T1 -> T1 -> T1
fadd z1 z2 =
  case orb (is_nan0 z1) (is_nan0 z2) of {
   True -> nans (Cons z1 (Cons z2 Nil));
   False ->
    case andb (is_infinity z1) (is_infinity z2) of {
     True ->
      case negb
             (eq_op bool_eqType (unsafeCoerce sign z1)
               (unsafeCoerce sign z2)) of {
       True -> nans Nil;
       False -> z1};
     False ->
      case is_infinity z1 of {
       True -> z1;
       False ->
        case is_infinity z2 of {
         True -> z2;
         False ->
          case andb (is_zero z1) (is_zero z2) of {
           True ->
            case negb
                   (eq_op bool_eqType (unsafeCoerce sign z1)
                     (unsafeCoerce sign z2)) of {
             True -> pos_zero;
             False -> z1};
           False ->
            case is_zero z1 of {
             True -> z2;
             False ->
              case is_zero z2 of {
               True -> z1;
               False ->
                case eq_op t_eqType (unsafeCoerce z1) (unsafeCoerce opp0 z2) of {
                 True -> pos_zero;
                 False -> add9 z1 z2}}}}}}}}

fsub :: T1 -> T1 -> T1
fsub z1 z2 =
  case orb (is_nan0 z1) (is_nan0 z2) of {
   True -> nans (Cons z1 (Cons z2 Nil));
   False ->
    case andb (is_infinity z1) (is_infinity z2) of {
     True ->
      case eq_op bool_eqType (unsafeCoerce sign z1) (unsafeCoerce sign z2) of {
       True -> nans Nil;
       False -> z1};
     False ->
      case is_infinity z1 of {
       True -> z1;
       False ->
        case is_infinity z2 of {
         True -> opp0 z2;
         False ->
          case andb (is_zero z1) (is_zero z2) of {
           True ->
            case eq_op bool_eqType (unsafeCoerce sign z1)
                   (unsafeCoerce sign z2) of {
             True -> pos_zero;
             False -> z1};
           False ->
            case is_zero z2 of {
             True -> z1;
             False ->
              case is_zero z1 of {
               True -> opp0 z2;
               False ->
                case eq_op t_eqType (unsafeCoerce z1) (unsafeCoerce z2) of {
                 True -> pos_zero;
                 False -> sub7 z1 z2}}}}}}}}

fmul :: T1 -> T1 -> T1
fmul z1 z2 =
  case orb (is_nan0 z1) (is_nan0 z2) of {
   True -> nans (Cons z1 (Cons z2 Nil));
   False ->
    case andb (is_infinity z1) (is_zero z2) of {
     True -> nans Nil;
     False ->
      case andb (is_infinity z2) (is_zero z1) of {
       True -> nans Nil;
       False ->
        case andb (is_infinity z1) (is_infinity z2) of {
         True ->
          case eq_op bool_eqType (unsafeCoerce sign z1)
                 (unsafeCoerce sign z2) of {
           True -> pos_infinity;
           False -> neg_infinity};
         False ->
          case eq_op bool_eqType
                 (unsafeCoerce andb (is_infinity z2) (sign z1))
                 (unsafeCoerce sign z2) of {
           True -> pos_infinity;
           False ->
            case eq_op bool_eqType
                   (unsafeCoerce andb (is_infinity z1) (sign z1))
                   (unsafeCoerce sign z2) of {
             True -> pos_infinity;
             False ->
              case negb
                     (eq_op bool_eqType
                       (unsafeCoerce andb (is_infinity z2) (sign z1))
                       (unsafeCoerce sign z2)) of {
               True -> neg_infinity;
               False ->
                case negb
                       (eq_op bool_eqType
                         (unsafeCoerce andb (is_infinity z1) (sign z1))
                         (unsafeCoerce sign z2)) of {
                 True -> neg_infinity;
                 False ->
                  case andb (is_zero z1) (is_zero z2) of {
                   True ->
                    case eq_op bool_eqType (unsafeCoerce sign z1)
                           (unsafeCoerce sign z2) of {
                     True -> pos_zero;
                     False -> neg_zero};
                   False -> mul6 z1 z2}}}}}}}}}

fdiv :: T1 -> T1 -> T1
fdiv z1 z2 =
  case orb (is_nan0 z1) (is_nan0 z2) of {
   True -> nans (Cons z1 (Cons z2 Nil));
   False ->
    case andb (is_infinity z1) (is_infinity z2) of {
     True -> nans Nil;
     False ->
      case andb (is_zero z2) (is_zero z1) of {
       True -> nans (Cons z1 (Cons z2 Nil));
       False ->
        case eq_op bool_eqType (unsafeCoerce andb (is_infinity z1) (sign z1))
               (unsafeCoerce sign z2) of {
         True -> pos_infinity;
         False ->
          case negb
                 (eq_op bool_eqType
                   (unsafeCoerce andb (is_infinity z1) (sign z1))
                   (unsafeCoerce sign z2)) of {
           True -> neg_infinity;
           False ->
            case eq_op bool_eqType
                   (unsafeCoerce andb (is_infinity z2) (sign z1))
                   (unsafeCoerce sign z2) of {
             True -> pos_zero;
             False ->
              case negb
                     (eq_op bool_eqType
                       (unsafeCoerce andb (is_infinity z2) (sign z1))
                       (unsafeCoerce sign z2)) of {
               True -> neg_zero;
               False ->
                case eq_op bool_eqType
                       (unsafeCoerce andb (is_zero z1) (sign z1))
                       (unsafeCoerce sign z2) of {
                 True -> pos_zero;
                 False ->
                  case negb
                         (eq_op bool_eqType
                           (unsafeCoerce andb (is_zero z1) (sign z1))
                           (unsafeCoerce sign z2)) of {
                   True -> neg_zero;
                   False ->
                    case eq_op bool_eqType
                           (unsafeCoerce andb (is_zero z2) (sign z1))
                           (unsafeCoerce sign z2) of {
                     True -> pos_infinity;
                     False ->
                      case negb
                             (eq_op bool_eqType
                               (unsafeCoerce andb (is_zero z2) (sign z1))
                               (unsafeCoerce sign z2)) of {
                       True -> pos_infinity;
                       False -> div3 z1 z2}}}}}}}}}}}

fmin :: T1 -> T1 -> T1
fmin z1 z2 =
  case orb (is_nan0 z1) (is_nan0 z2) of {
   True -> nans (Cons z1 (Cons z2 Nil));
   False ->
    case orb (eq_op t_eqType (unsafeCoerce z1) (unsafeCoerce neg_infinity))
           (eq_op t_eqType (unsafeCoerce z2) (unsafeCoerce neg_infinity)) of {
     True -> neg_infinity;
     False ->
      case eq_op t_eqType (unsafeCoerce z1) (unsafeCoerce pos_infinity) of {
       True -> z2;
       False ->
        case eq_op t_eqType (unsafeCoerce z2) (unsafeCoerce pos_infinity) of {
         True -> z1;
         False ->
          case negb
                 (eq_op bool_eqType
                   (unsafeCoerce andb (andb (is_zero z1) (is_zero z2))
                     (sign z1)) (unsafeCoerce sign z2)) of {
           True -> neg_zero;
           False -> case cmp1 Clt z1 z2 of {
                     True -> z1;
                     False -> z2}}}}}}

fmax :: T1 -> T1 -> T1
fmax z1 z2 =
  case orb (is_nan0 z1) (is_nan0 z2) of {
   True -> nans (Cons z1 (Cons z2 Nil));
   False ->
    case orb (eq_op t_eqType (unsafeCoerce z1) (unsafeCoerce pos_infinity))
           (eq_op t_eqType (unsafeCoerce z2) (unsafeCoerce pos_infinity)) of {
     True -> pos_infinity;
     False ->
      case eq_op t_eqType (unsafeCoerce z1) (unsafeCoerce neg_infinity) of {
       True -> z2;
       False ->
        case eq_op t_eqType (unsafeCoerce z2) (unsafeCoerce neg_infinity) of {
         True -> z1;
         False ->
          case negb
                 (eq_op bool_eqType
                   (unsafeCoerce andb (andb (is_zero z1) (is_zero z2))
                     (sign z1)) (unsafeCoerce sign z2)) of {
           True -> pos_zero;
           False -> case cmp1 Cgt z1 z2 of {
                     True -> z1;
                     False -> z2}}}}}}

fcopysign :: T1 -> T1 -> T1
fcopysign f1 f2 =
  case eq_op bool_eqType (unsafeCoerce sign f1) (unsafeCoerce sign f2) of {
   True -> f1;
   False -> opp0 f1}

fabs :: T1 -> T1
fabs z =
  case is_nan0 z of {
   True -> set_sign False z;
   False ->
    case is_infinity z of {
     True -> pos_infinity;
     False ->
      case is_zero z of {
       True -> pos_zero;
       False -> case cmp1 Cgt z pos_zero of {
                 True -> z;
                 False -> opp0 z}}}}

fneg :: T1 -> T1
fneg z =
  case is_nan0 z of {
   True -> set_sign (negb (sign z)) z;
   False -> opp0 z}

fsqrt :: T1 -> T1
fsqrt z =
  case is_nan0 z of {
   True -> nans (Cons z Nil);
   False ->
    case sign z of {
     True -> nans Nil;
     False ->
      case eq_op t_eqType (unsafeCoerce z) (unsafeCoerce pos_infinity) of {
       True -> pos_infinity;
       False -> case is_zero z of {
                 True -> z;
                 False -> sqrt z}}}}

fceil :: T1 -> T1
fceil z =
  case is_nan0 z of {
   True -> nans (Cons z Nil);
   False ->
    case is_infinity z of {
     True -> z;
     False ->
      case is_zero z of {
       True -> z;
       False ->
        case andb (cmp1 Clt z neg_zero) (cmp1 Cgt z (bofZ0 (Zneg XH))) of {
         True -> neg_zero;
         False -> ceil z}}}}

ffloor :: T1 -> T1
ffloor z =
  case is_nan0 z of {
   True -> nans (Cons z Nil);
   False ->
    case is_infinity z of {
     True -> z;
     False ->
      case is_zero z of {
       True -> z;
       False ->
        case andb (cmp1 Cgt z pos_zero) (cmp1 Clt z (bofZ0 (Zpos XH))) of {
         True -> pos_zero;
         False -> floor z}}}}

ftrunc :: T1 -> T1
ftrunc z =
  case is_nan0 z of {
   True -> nans (Cons z Nil);
   False ->
    case is_infinity z of {
     True -> z;
     False ->
      case is_zero z of {
       True -> z;
       False ->
        case andb (cmp1 Cgt z pos_zero) (cmp1 Clt z (bofZ0 (Zpos XH))) of {
         True -> pos_zero;
         False ->
          case andb (cmp1 Clt z neg_zero) (cmp1 Cgt z (bofZ0 (Zneg XH))) of {
           True -> neg_zero;
           False -> trunc z}}}}}

fnearest :: T1 -> T1
fnearest z =
  case is_nan0 z of {
   True -> nans (Cons z Nil);
   False ->
    case is_infinity z of {
     True -> z;
     False ->
      case is_zero z of {
       True -> z;
       False ->
        case andb (cmp1 Cgt z pos_zero)
               (cmp1 Clt z (normalise (Zpos XH) (Zneg XH))) of {
         True -> pos_zero;
         False ->
          case andb (cmp1 Clt z neg_zero)
                 (cmp1 Cgt z (normalise (Zneg XH) (Zneg XH))) of {
           True -> neg_zero;
           False -> nearest z}}}}}

to_int_range :: (Mixin_of0 a1) -> Z -> Z -> Z -> Option a1
to_int_range m min0 max1 i =
  case andb (geb i min0) (leb1 i max1) of {
   True -> Some (int_of_Z m i);
   False -> None}

ui32_trunc :: T1 -> Option Sort
ui32_trunc z =
  bind (to_int_range i32m Z0 max_unsigned1) (trunco z)

si32_trunc :: T1 -> Option Sort
si32_trunc z =
  bind (to_int_range i32m min_signed1 max_signed1) (trunco z)

ui64_trunc :: T1 -> Option Sort
ui64_trunc z =
  bind (to_int_range i64m Z0 max_unsigned2) (trunco z)

si64_trunc :: T1 -> Option Sort
si64_trunc z =
  bind (to_int_range i64m min_signed2 max_signed1) (trunco z)

convert_ui32 :: Sort -> T1
convert_ui32 i =
  bofZ0 (z_of_uint i32m i)

convert_si32 :: Sort -> T1
convert_si32 i =
  bofZ0 (z_of_sint i32m i)

convert_ui64 :: Sort -> T1
convert_ui64 i =
  bofZ0 (z_of_uint i64m i)

convert_si64 :: Sort -> T1
convert_si64 i =
  bofZ0 (z_of_sint i64m i)

tmixin1 :: Mixin_of1 T1
tmixin1 =
  Mixin1 pos_zero fneg fabs fsqrt fceil ffloor ftrunc fnearest fadd fsub fmul
    fdiv fmin fmax fcopysign (cmp1 Ceq) (cmp1 Clt) (cmp1 Cgt) (cmp1 Cle)
    (cmp1 Cge) ui32_trunc si32_trunc ui64_trunc si64_trunc convert_ui32
    convert_si32 convert_ui64 convert_si64

cT1 :: Type1
cT1 =
  Class0 (unsafeCoerce t_eqMixin) (unsafeCoerce tmixin1)

class3 :: Class_of0 Sort1
class3 =
  cT1

eqType1 :: Type
eqType1 =
  base0 class3

eqb5 :: Binary_float -> Binary_float -> Bool
eqb5 v1 v2 =
  is_left (eq_dec4 v1 v2)

eqbP1 :: Axiom Binary_float
eqbP1 =
  eq_dec_Equality_axiom eq_dec4

t_eqMixin0 :: Mixin_of Binary_float
t_eqMixin0 =
  Mixin eqb5 eqbP1

t_eqType0 :: Type
t_eqType0 =
  unsafeCoerce t_eqMixin0

is_nan1 :: T2 -> Bool
is_nan1 =
  is_nan prec0 emax0

sign0 :: T2 -> Bool
sign0 =
  bsign prec0 emax0

is_zero0 :: T2 -> Bool
is_zero0 z =
  case z of {
   B754_zero _ -> True;
   _ -> False}

is_infinity0 :: T2 -> Bool
is_infinity0 z =
  case z of {
   B754_infinity _ -> True;
   _ -> False}

pos_infinity0 :: T2
pos_infinity0 =
  B754_infinity False

neg_infinity0 :: T2
neg_infinity0 =
  B754_infinity True

pos_zero0 :: T2
pos_zero0 =
  B754_zero False

neg_zero0 :: T2
neg_zero0 =
  B754_zero True

canonical_pl0 :: Positive
canonical_pl0 =
  shift_pos (sub0 (to_pos prec0) (XO XH)) XH

is_canonical0 :: T2 -> Bool
is_canonical0 z =
  case z of {
   B754_nan _ pl ->
    eq_op pos_eqType (unsafeCoerce pl) (unsafeCoerce canonical_pl0);
   _ -> False}

pl_arithmetic0 :: Positive -> Bool
pl_arithmetic0 pl =
  eq_op z_eqType (unsafeCoerce (Zpos (digits2_pos pl)))
    (unsafeCoerce sub2 prec0 (Zpos XH))

canonical_nan0 :: Bool -> T2
canonical_nan0 s =
  B754_nan s canonical_pl0

unspec_canonical_nan0 :: T2
unspec_canonical_nan0 =
  canonical_nan0 False

make_arithmetic0 :: Positive -> Positive
make_arithmetic0 __top_assumption_ =
  let {_evar_0_ = \_ -> __top_assumption_} in
  let {
   _evar_0_0 = \_ ->
    let {_evar_0_0 = \_ _ -> false_rec} in
    let {_evar_0_1 = \_ -> lor __top_assumption_ canonical_pl0} in
    let {_evar_0_2 = \_ -> false_rec} in
    case prec0 of {
     Z0 -> _evar_0_0 __ __;
     Zpos x -> _evar_0_1 x;
     Zneg x -> _evar_0_2 x}}
  in
  case pl_arithmetic0 __top_assumption_ of {
   True -> _evar_0_ __;
   False -> _evar_0_0 __}

unspec_nan_pl0 :: Positive
unspec_nan_pl0 =
  ssr_have
    (let {_evar_0_ = \_ -> false_rec} in
     let {_evar_0_0 = \_ -> false_rec} in
     let {_evar_0_1 = \_ pl -> pl} in
     let {_evar_0_2 = \_ _ _ -> false_rec} in
     case default_nan0 of {
      B754_zero x -> _evar_0_ x;
      B754_infinity x -> _evar_0_0 x;
      B754_nan x x0 -> _evar_0_1 x x0;
      B754_finite x x0 x1 -> _evar_0_2 x x0 x1}) (\pl -> pl)

unspec_arithmetic_nan_pl0 :: Positive
unspec_arithmetic_nan_pl0 =
  make_arithmetic0 unspec_nan_pl0

unspec_arithmetic_nan0 :: T2
unspec_arithmetic_nan0 =
  B754_nan True (proj1_sig unspec_arithmetic_nan_pl0)

unspec_nan_nan0 :: T2
unspec_nan_nan0 =
  unspec_arithmetic_nan0

unspec_nan0 :: T2
unspec_nan0 =
  proj1_sig unspec_nan_nan0

opp1 :: T2 -> T2
opp1 =
  bopp prec0 emax0 (\_ -> unspec_nan0)

normalise0 :: Z -> Z -> T2
normalise0 m e =
  binary_normalize prec0 emax0 Mode_NE m e False

nans0 :: (List T2) -> T2
nans0 zs =
  case all is_canonical0 (filter is_nan1 zs) of {
   True -> unspec_canonical_nan0;
   False -> unspec_arithmetic_nan0}

sqrt0 :: T2 -> T2
sqrt0 z =
  bsqrt prec0 emax0 (\z0 -> nans0 (Cons z0 Nil)) Mode_NE z

zofB_param0 :: (Z -> Z -> Z) -> (Z -> Z -> Z) -> T2 -> Option Z
zofB_param0 divP divN z =
  case z of {
   B754_zero _ -> Some Z0;
   B754_finite s m e0 ->
    case e0 of {
     Z0 -> Some (cond_Zopp s (Zpos m));
     Zpos e -> Some
      (mul1 (cond_Zopp s (Zpos m)) (pow_pos (radix_val radix2) e));
     Zneg e -> Some
      (cond_Zopp s
        (case s of {
          True -> divN (Zpos m) (pow_pos (radix_val radix2) e);
          False -> divP (Zpos m) (pow_pos (radix_val radix2) e)}))};
   _ -> None}

div_down0 :: Z -> Z -> Z
div_down0 =
  div0

div_up0 :: Z -> Z -> Z
div_up0 a b =
  add3 (case zeq_bool (modulo a b) Z0 of {
         True -> Z0;
         False -> Zpos XH}) (div0 a b)

div_near0 :: Z -> Z -> Z
div_near0 a b =
  case ltb0 (modulo a b) (div0 b (Zpos (XO XH))) of {
   True -> div_down0 a b;
   False ->
    case gtb (modulo a b) (div0 b (Zpos (XO XH))) of {
     True -> div_up0 a b;
     False ->
      case even (div_down0 a b) of {
       True -> div_down0 a b;
       False -> div_up0 a b}}}

ceilo0 :: T2 -> Option Z
ceilo0 =
  zofB_param0 div_up0 div_down0

flooro0 :: T2 -> Option Z
flooro0 =
  zofB_param0 div_down0 div_up0

trunco0 :: T2 -> Option Z
trunco0 =
  zofB_param0 div_down0 div_down0

nearesto0 :: T2 -> Option Z
nearesto0 =
  zofB_param0 div_near0 div_near0

bofZ1 :: Z -> T2
bofZ1 =
  bofZ prec0 emax0

floatify0 :: (T2 -> Option Z) -> T2 -> T2
floatify0 f z =
  case f z of {
   Some i -> bofZ1 i;
   None -> z}

ceil0 :: T2 -> T2
ceil0 =
  floatify0 ceilo0

floor0 :: T2 -> T2
floor0 =
  floatify0 flooro0

trunc0 :: T2 -> T2
trunc0 =
  floatify0 trunco0

nearest0 :: T2 -> T2
nearest0 =
  floatify0 nearesto0

set_sign0 :: Bool -> T2 -> T2
set_sign0 s z =
  case z of {
   B754_zero _ -> B754_zero s;
   B754_infinity _ -> B754_infinity s;
   B754_nan _ pl -> B754_nan s pl;
   B754_finite _ m e -> B754_finite s m e}

fadd0 :: T2 -> T2 -> T2
fadd0 z1 z2 =
  case orb (is_nan1 z1) (is_nan1 z2) of {
   True -> nans0 (Cons z1 (Cons z2 Nil));
   False ->
    case andb (is_infinity0 z1) (is_infinity0 z2) of {
     True ->
      case negb
             (eq_op bool_eqType (unsafeCoerce sign0 z1)
               (unsafeCoerce sign0 z2)) of {
       True -> nans0 Nil;
       False -> z1};
     False ->
      case is_infinity0 z1 of {
       True -> z1;
       False ->
        case is_infinity0 z2 of {
         True -> z2;
         False ->
          case andb (is_zero0 z1) (is_zero0 z2) of {
           True ->
            case negb
                   (eq_op bool_eqType (unsafeCoerce sign0 z1)
                     (unsafeCoerce sign0 z2)) of {
             True -> pos_zero0;
             False -> z1};
           False ->
            case is_zero0 z1 of {
             True -> z2;
             False ->
              case is_zero0 z2 of {
               True -> z1;
               False ->
                case eq_op t_eqType0 (unsafeCoerce z1) (unsafeCoerce opp1 z2) of {
                 True -> pos_zero0;
                 False -> add10 z1 z2}}}}}}}}

fsub0 :: T2 -> T2 -> T2
fsub0 z1 z2 =
  case orb (is_nan1 z1) (is_nan1 z2) of {
   True -> nans0 (Cons z1 (Cons z2 Nil));
   False ->
    case andb (is_infinity0 z1) (is_infinity0 z2) of {
     True ->
      case eq_op bool_eqType (unsafeCoerce sign0 z1) (unsafeCoerce sign0 z2) of {
       True -> nans0 Nil;
       False -> z1};
     False ->
      case is_infinity0 z1 of {
       True -> z1;
       False ->
        case is_infinity0 z2 of {
         True -> opp1 z2;
         False ->
          case andb (is_zero0 z1) (is_zero0 z2) of {
           True ->
            case eq_op bool_eqType (unsafeCoerce sign0 z1)
                   (unsafeCoerce sign0 z2) of {
             True -> pos_zero0;
             False -> z1};
           False ->
            case is_zero0 z2 of {
             True -> z1;
             False ->
              case is_zero0 z1 of {
               True -> opp1 z2;
               False ->
                case eq_op t_eqType0 (unsafeCoerce z1) (unsafeCoerce z2) of {
                 True -> pos_zero0;
                 False -> sub8 z1 z2}}}}}}}}

fmul0 :: T2 -> T2 -> T2
fmul0 z1 z2 =
  case orb (is_nan1 z1) (is_nan1 z2) of {
   True -> nans0 (Cons z1 (Cons z2 Nil));
   False ->
    case andb (is_infinity0 z1) (is_zero0 z2) of {
     True -> nans0 Nil;
     False ->
      case andb (is_infinity0 z2) (is_zero0 z1) of {
       True -> nans0 Nil;
       False ->
        case andb (is_infinity0 z1) (is_infinity0 z2) of {
         True ->
          case eq_op bool_eqType (unsafeCoerce sign0 z1)
                 (unsafeCoerce sign0 z2) of {
           True -> pos_infinity0;
           False -> neg_infinity0};
         False ->
          case eq_op bool_eqType
                 (unsafeCoerce andb (is_infinity0 z2) (sign0 z1))
                 (unsafeCoerce sign0 z2) of {
           True -> pos_infinity0;
           False ->
            case eq_op bool_eqType
                   (unsafeCoerce andb (is_infinity0 z1) (sign0 z1))
                   (unsafeCoerce sign0 z2) of {
             True -> pos_infinity0;
             False ->
              case negb
                     (eq_op bool_eqType
                       (unsafeCoerce andb (is_infinity0 z2) (sign0 z1))
                       (unsafeCoerce sign0 z2)) of {
               True -> neg_infinity0;
               False ->
                case negb
                       (eq_op bool_eqType
                         (unsafeCoerce andb (is_infinity0 z1) (sign0 z1))
                         (unsafeCoerce sign0 z2)) of {
                 True -> neg_infinity0;
                 False ->
                  case andb (is_zero0 z1) (is_zero0 z2) of {
                   True ->
                    case eq_op bool_eqType (unsafeCoerce sign0 z1)
                           (unsafeCoerce sign0 z2) of {
                     True -> pos_zero0;
                     False -> neg_zero0};
                   False -> mul7 z1 z2}}}}}}}}}

fdiv0 :: T2 -> T2 -> T2
fdiv0 z1 z2 =
  case orb (is_nan1 z1) (is_nan1 z2) of {
   True -> nans0 (Cons z1 (Cons z2 Nil));
   False ->
    case andb (is_infinity0 z1) (is_infinity0 z2) of {
     True -> nans0 Nil;
     False ->
      case andb (is_zero0 z2) (is_zero0 z1) of {
       True -> nans0 (Cons z1 (Cons z2 Nil));
       False ->
        case eq_op bool_eqType
               (unsafeCoerce andb (is_infinity0 z1) (sign0 z1))
               (unsafeCoerce sign0 z2) of {
         True -> pos_infinity0;
         False ->
          case negb
                 (eq_op bool_eqType
                   (unsafeCoerce andb (is_infinity0 z1) (sign0 z1))
                   (unsafeCoerce sign0 z2)) of {
           True -> neg_infinity0;
           False ->
            case eq_op bool_eqType
                   (unsafeCoerce andb (is_infinity0 z2) (sign0 z1))
                   (unsafeCoerce sign0 z2) of {
             True -> pos_zero0;
             False ->
              case negb
                     (eq_op bool_eqType
                       (unsafeCoerce andb (is_infinity0 z2) (sign0 z1))
                       (unsafeCoerce sign0 z2)) of {
               True -> neg_zero0;
               False ->
                case eq_op bool_eqType
                       (unsafeCoerce andb (is_zero0 z1) (sign0 z1))
                       (unsafeCoerce sign0 z2) of {
                 True -> pos_zero0;
                 False ->
                  case negb
                         (eq_op bool_eqType
                           (unsafeCoerce andb (is_zero0 z1) (sign0 z1))
                           (unsafeCoerce sign0 z2)) of {
                   True -> neg_zero0;
                   False ->
                    case eq_op bool_eqType
                           (unsafeCoerce andb (is_zero0 z2) (sign0 z1))
                           (unsafeCoerce sign0 z2) of {
                     True -> pos_infinity0;
                     False ->
                      case negb
                             (eq_op bool_eqType
                               (unsafeCoerce andb (is_zero0 z2) (sign0 z1))
                               (unsafeCoerce sign0 z2)) of {
                       True -> pos_infinity0;
                       False -> div4 z1 z2}}}}}}}}}}}

fmin0 :: T2 -> T2 -> T2
fmin0 z1 z2 =
  case orb (is_nan1 z1) (is_nan1 z2) of {
   True -> nans0 (Cons z1 (Cons z2 Nil));
   False ->
    case orb (eq_op t_eqType0 (unsafeCoerce z1) (unsafeCoerce neg_infinity0))
           (eq_op t_eqType0 (unsafeCoerce z2) (unsafeCoerce neg_infinity0)) of {
     True -> neg_infinity0;
     False ->
      case eq_op t_eqType0 (unsafeCoerce z1) (unsafeCoerce pos_infinity0) of {
       True -> z2;
       False ->
        case eq_op t_eqType0 (unsafeCoerce z2) (unsafeCoerce pos_infinity0) of {
         True -> z1;
         False ->
          case negb
                 (eq_op bool_eqType
                   (unsafeCoerce andb (andb (is_zero0 z1) (is_zero0 z2))
                     (sign0 z1)) (unsafeCoerce sign0 z2)) of {
           True -> neg_zero0;
           False -> case cmp2 Clt z1 z2 of {
                     True -> z1;
                     False -> z2}}}}}}

fmax0 :: T2 -> T2 -> T2
fmax0 z1 z2 =
  case orb (is_nan1 z1) (is_nan1 z2) of {
   True -> nans0 (Cons z1 (Cons z2 Nil));
   False ->
    case orb (eq_op t_eqType0 (unsafeCoerce z1) (unsafeCoerce pos_infinity0))
           (eq_op t_eqType0 (unsafeCoerce z2) (unsafeCoerce pos_infinity0)) of {
     True -> pos_infinity0;
     False ->
      case eq_op t_eqType0 (unsafeCoerce z1) (unsafeCoerce neg_infinity0) of {
       True -> z2;
       False ->
        case eq_op t_eqType0 (unsafeCoerce z2) (unsafeCoerce neg_infinity0) of {
         True -> z1;
         False ->
          case negb
                 (eq_op bool_eqType
                   (unsafeCoerce andb (andb (is_zero0 z1) (is_zero0 z2))
                     (sign0 z1)) (unsafeCoerce sign0 z2)) of {
           True -> pos_zero0;
           False -> case cmp2 Cgt z1 z2 of {
                     True -> z1;
                     False -> z2}}}}}}

fcopysign0 :: T2 -> T2 -> T2
fcopysign0 f1 f2 =
  case eq_op bool_eqType (unsafeCoerce sign0 f1) (unsafeCoerce sign0 f2) of {
   True -> f1;
   False -> opp1 f1}

fabs0 :: T2 -> T2
fabs0 z =
  case is_nan1 z of {
   True -> set_sign0 False z;
   False ->
    case is_infinity0 z of {
     True -> pos_infinity0;
     False ->
      case is_zero0 z of {
       True -> pos_zero0;
       False -> case cmp2 Cgt z pos_zero0 of {
                 True -> z;
                 False -> opp1 z}}}}

fneg0 :: T2 -> T2
fneg0 z =
  case is_nan1 z of {
   True -> set_sign0 (negb (sign0 z)) z;
   False -> opp1 z}

fsqrt0 :: T2 -> T2
fsqrt0 z =
  case is_nan1 z of {
   True -> nans0 (Cons z Nil);
   False ->
    case sign0 z of {
     True -> nans0 Nil;
     False ->
      case eq_op t_eqType0 (unsafeCoerce z) (unsafeCoerce pos_infinity0) of {
       True -> pos_infinity0;
       False -> case is_zero0 z of {
                 True -> z;
                 False -> sqrt0 z}}}}

fceil0 :: T2 -> T2
fceil0 z =
  case is_nan1 z of {
   True -> nans0 (Cons z Nil);
   False ->
    case is_infinity0 z of {
     True -> z;
     False ->
      case is_zero0 z of {
       True -> z;
       False ->
        case andb (cmp2 Clt z neg_zero0) (cmp2 Cgt z (bofZ1 (Zneg XH))) of {
         True -> neg_zero0;
         False -> ceil0 z}}}}

ffloor0 :: T2 -> T2
ffloor0 z =
  case is_nan1 z of {
   True -> nans0 (Cons z Nil);
   False ->
    case is_infinity0 z of {
     True -> z;
     False ->
      case is_zero0 z of {
       True -> z;
       False ->
        case andb (cmp2 Cgt z pos_zero0) (cmp2 Clt z (bofZ1 (Zpos XH))) of {
         True -> pos_zero0;
         False -> floor0 z}}}}

ftrunc0 :: T2 -> T2
ftrunc0 z =
  case is_nan1 z of {
   True -> nans0 (Cons z Nil);
   False ->
    case is_infinity0 z of {
     True -> z;
     False ->
      case is_zero0 z of {
       True -> z;
       False ->
        case andb (cmp2 Cgt z pos_zero0) (cmp2 Clt z (bofZ1 (Zpos XH))) of {
         True -> pos_zero0;
         False ->
          case andb (cmp2 Clt z neg_zero0) (cmp2 Cgt z (bofZ1 (Zneg XH))) of {
           True -> neg_zero0;
           False -> trunc0 z}}}}}

fnearest0 :: T2 -> T2
fnearest0 z =
  case is_nan1 z of {
   True -> nans0 (Cons z Nil);
   False ->
    case is_infinity0 z of {
     True -> z;
     False ->
      case is_zero0 z of {
       True -> z;
       False ->
        case andb (cmp2 Cgt z pos_zero0)
               (cmp2 Clt z (normalise0 (Zpos XH) (Zneg XH))) of {
         True -> pos_zero0;
         False ->
          case andb (cmp2 Clt z neg_zero0)
                 (cmp2 Cgt z (normalise0 (Zneg XH) (Zneg XH))) of {
           True -> neg_zero0;
           False -> nearest0 z}}}}}

to_int_range0 :: (Mixin_of0 a1) -> Z -> Z -> Z -> Option a1
to_int_range0 m min0 max1 i =
  case andb (geb i min0) (leb1 i max1) of {
   True -> Some (int_of_Z m i);
   False -> None}

ui32_trunc0 :: T2 -> Option Sort
ui32_trunc0 z =
  bind (to_int_range0 i32m Z0 max_unsigned1) (trunco0 z)

si32_trunc0 :: T2 -> Option Sort
si32_trunc0 z =
  bind (to_int_range0 i32m min_signed1 max_signed1) (trunco0 z)

ui64_trunc0 :: T2 -> Option Sort
ui64_trunc0 z =
  bind (to_int_range0 i64m Z0 max_unsigned2) (trunco0 z)

si64_trunc0 :: T2 -> Option Sort
si64_trunc0 z =
  bind (to_int_range0 i64m min_signed2 max_signed1) (trunco0 z)

convert_ui0 :: Sort -> T2
convert_ui0 i =
  bofZ1 (z_of_uint i32m i)

convert_si0 :: Sort -> T2
convert_si0 i =
  bofZ1 (z_of_sint i32m i)

convert_ui1 :: Sort -> T2
convert_ui1 i =
  bofZ1 (z_of_uint i64m i)

convert_si1 :: Sort -> T2
convert_si1 i =
  bofZ1 (z_of_sint i64m i)

tmixin2 :: Mixin_of1 T2
tmixin2 =
  Mixin1 pos_zero0 fneg0 fabs0 fsqrt0 fceil0 ffloor0 ftrunc0 fnearest0 fadd0
    fsub0 fmul0 fdiv0 fmin0 fmax0 fcopysign0 (cmp2 Ceq) (cmp2 Clt) (cmp2 Cgt)
    (cmp2 Cle) (cmp2 Cge) ui32_trunc0 si32_trunc0 ui64_trunc0 si64_trunc0
    convert_ui0 convert_si0 convert_ui1 convert_si1

cT2 :: Type1
cT2 =
  Class0 (unsafeCoerce t_eqMixin0) (unsafeCoerce tmixin2)

class4 :: Class_of0 Sort1
class4 =
  cT2

eqType2 :: Type
eqType2 =
  base0 class4

f32 :: Type
f32 =
  eqType1

f32r :: Class_of0 Sort
f32r =
  class3

f32t :: Type1
f32t =
  f32r

f32m :: Mixin_of1 Sort
f32m =
  mixin0 f32r

f64 :: Type
f64 =
  eqType2

f64r :: Class_of0 Sort
f64r =
  class4

f64t :: Type1
f64t =
  f64r

f64m :: Mixin_of1 Sort
f64m =
  mixin0 f64r

wasm_demote :: Sort -> Sort
wasm_demote z =
  case is_canonical0 (unsafeCoerce z) of {
   True -> unsafeCoerce nans Nil;
   False ->
    case is_nan1 (unsafeCoerce z) of {
     True -> unsafeCoerce nans (Cons (bofZ0 (of_nat0 (S O))) Nil);
     False ->
      unsafeCoerce bconv prec0 emax0 prec emax (\_ -> unspec_nan_nan) Mode_NE
        z}}

wasm_promote :: Sort -> Sort
wasm_promote z =
  case is_canonical (unsafeCoerce z) of {
   True -> unsafeCoerce nans0 Nil;
   False ->
    case is_nan0 (unsafeCoerce z) of {
     True -> unsafeCoerce nans0 (Cons (bofZ1 (of_nat0 (S O))) Nil);
     False ->
      unsafeCoerce bconv prec emax prec0 emax0 (\_ -> unspec_nan_nan0)
        Mode_NE z}}

wasm_bool :: Bool -> Sort
wasm_bool b =
  case b of {
   True -> unsafeCoerce one1;
   False -> unsafeCoerce zero1}

int32_minus_one :: Sort
int32_minus_one =
  unsafeCoerce mone1

type Byte = Int0

type Bytes = List Byte

bytes_takefill :: Byte -> Nat -> Bytes -> Bytes
bytes_takefill a n aas =
  case n of {
   O -> Nil;
   S n' ->
    case aas of {
     Nil -> Cons a (bytes_takefill a n' aas);
     Cons a' aas' -> Cons a' (bytes_takefill a n' aas')}}

type Mem_length_t mem_t = mem_t -> N

type Mem_lookup_t mem_t = N -> mem_t -> Option Byte

type Mem_update_t mem_t = N -> Byte -> mem_t -> Option mem_t

data Memory_list =
   Build_memory_list Byte (List Byte)

ml_init :: Memory_list -> Byte
ml_init m =
  case m of {
   Build_memory_list ml_init0 _ -> ml_init0}

ml_data :: Memory_list -> List Byte
ml_data m =
  case m of {
   Build_memory_list _ ml_data0 -> ml_data0}

mem_length :: Mem_length_t Memory_list
mem_length ml =
  of_nat (length (ml_data ml))

mem_lookup :: Mem_lookup_t Memory_list
mem_lookup i ml =
  nth_error (ml_data ml) (to_nat0 i)

mem_update :: Mem_update_t Memory_list
mem_update i v ml =
  case ltb i (of_nat (length (ml_data ml))) of {
   True -> Some (Build_memory_list (ml_init ml)
    (cat (take (to_nat0 i) (ml_data ml))
      (cat (Cons v Nil) (drop (add (to_nat0 i) (S O)) (ml_data ml)))));
   False -> None}

bytes_of_int :: Nat -> Z -> List Int0
bytes_of_int n x =
  case n of {
   O -> Nil;
   S m -> Cons (repr0 x)
    (bytes_of_int m
      (div0 x (Zpos (XO (XO (XO (XO (XO (XO (XO (XO XH)))))))))))}

int_of_bytes :: (List Int0) -> Z
int_of_bytes l =
  case l of {
   Nil -> Z0;
   Cons b l' ->
    add3 (unsigned0 b)
      (mul1 (int_of_bytes l') (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
        XH))))))))))}

rev_if_be :: (List Int0) -> List Int0
rev_if_be l =
  case big_endian of {
   True -> rev l;
   False -> l}

encode_int :: Nat -> Z -> List Int0
encode_int sz x =
  rev_if_be (bytes_of_int sz x)

decode_int :: (List Int0) -> Z
decode_int b =
  int_of_bytes (rev_if_be b)

type Immediate = Nat

type Static_offset = N

type Alignment_exponent = N

serialise_i32 :: Sort -> Bytes
serialise_i32 i =
  encode_int (S (S (S (S O)))) (unsigned2 (unsafeCoerce i))

serialise_i64 :: Sort -> Bytes
serialise_i64 i =
  encode_int (S (S (S (S (S (S (S (S O)))))))) (unsigned3 (unsafeCoerce i))

serialise_f32 :: Sort -> Bytes
serialise_f32 f =
  encode_int (S (S (S (S O)))) (unsigned (to_bits (unsafeCoerce f)))

serialise_f64 :: Sort -> Bytes
serialise_f64 f =
  encode_int (S (S (S (S (S (S (S (S O))))))))
    (unsigned1 (to_bits0 (unsafeCoerce f)))

data Limits =
   Build_limits N (Option N)

data Memory =
   Build_memory Memory_list (Option N)

mem_data :: Memory -> Memory_list
mem_data m =
  case m of {
   Build_memory mem_data0 _ -> mem_data0}

mem_max_opt :: Memory -> Option N
mem_max_opt m =
  case m of {
   Build_memory _ mem_max_opt0 -> mem_max_opt0}

type Memory_type = Limits

data Value_type =
   T_i32
 | T_i64
 | T_f32
 | T_f64

data Packed_type =
   Tp_i8
 | Tp_i16
 | Tp_i32

data Mutability =
   MUT_immut
 | MUT_mut

data Global_type =
   Build_global_type Mutability Value_type

tg_t :: Global_type -> Value_type
tg_t g =
  case g of {
   Build_global_type _ tg_t0 -> tg_t0}

type Result_type = List Value_type

data Function_type =
   Tf Result_type Result_type

function_type_rect :: (Result_type -> Result_type -> a1) -> Function_type ->
                      a1
function_type_rect f f0 =
  case f0 of {
   Tf x x0 -> f x x0}

type Table_type =
  Limits
  -- singleton inductive, whose constructor was Build_table_type
  
data T_context =
   Build_t_context (List Function_type) (List Function_type) (List
                                                             Global_type) 
 (List Table_type) (List Memory_type) (List Value_type) (List
                                                        (List Value_type)) 
 (Option (List Value_type))

tc_types_t :: T_context -> List Function_type
tc_types_t t =
  case t of {
   Build_t_context tc_types_t0 _ _ _ _ _ _ _ -> tc_types_t0}

tc_func_t :: T_context -> List Function_type
tc_func_t t =
  case t of {
   Build_t_context _ tc_func_t0 _ _ _ _ _ _ -> tc_func_t0}

tc_global :: T_context -> List Global_type
tc_global t =
  case t of {
   Build_t_context _ _ tc_global0 _ _ _ _ _ -> tc_global0}

tc_table :: T_context -> List Table_type
tc_table t =
  case t of {
   Build_t_context _ _ _ tc_table0 _ _ _ _ -> tc_table0}

tc_memory :: T_context -> List Memory_type
tc_memory t =
  case t of {
   Build_t_context _ _ _ _ tc_memory0 _ _ _ -> tc_memory0}

tc_local :: T_context -> List Value_type
tc_local t =
  case t of {
   Build_t_context _ _ _ _ _ tc_local0 _ _ -> tc_local0}

tc_label :: T_context -> List (List Value_type)
tc_label t =
  case t of {
   Build_t_context _ _ _ _ _ _ tc_label0 _ -> tc_label0}

tc_return :: T_context -> Option (List Value_type)
tc_return t =
  case t of {
   Build_t_context _ _ _ _ _ _ _ tc_return0 -> tc_return0}

data Value =
   VAL_int32 Sort
 | VAL_int64 Sort
 | VAL_float32 Sort
 | VAL_float64 Sort

value_rect :: (Sort -> a1) -> (Sort -> a1) -> (Sort -> a1) -> (Sort -> a1) ->
              Value -> a1
value_rect f f0 f1 f2 v =
  case v of {
   VAL_int32 x -> f x;
   VAL_int64 x -> f0 x;
   VAL_float32 x -> f1 x;
   VAL_float64 x -> f2 x}

data Result =
   Result_values (List Value)
 | Result_trap

data Sx =
   SX_S
 | SX_U

data Unop_i =
   UOI_clz
 | UOI_ctz
 | UOI_popcnt

data Unop_f =
   UOF_neg
 | UOF_abs
 | UOF_ceil
 | UOF_floor
 | UOF_trunc
 | UOF_nearest
 | UOF_sqrt

data Unop =
   Unop_i0 Unop_i
 | Unop_f0 Unop_f

unop_rect :: (Unop_i -> a1) -> (Unop_f -> a1) -> Unop -> a1
unop_rect f f0 u =
  case u of {
   Unop_i0 x -> f x;
   Unop_f0 x -> f0 x}

unop_rec :: (Unop_i -> a1) -> (Unop_f -> a1) -> Unop -> a1
unop_rec =
  unop_rect

data Binop_i =
   BOI_add
 | BOI_sub
 | BOI_mul
 | BOI_div Sx
 | BOI_rem Sx
 | BOI_and
 | BOI_or
 | BOI_xor
 | BOI_shl
 | BOI_shr Sx
 | BOI_rotl
 | BOI_rotr

data Binop_f =
   BOF_add
 | BOF_sub
 | BOF_mul
 | BOF_div
 | BOF_min
 | BOF_max
 | BOF_copysign

data Binop =
   Binop_i0 Binop_i
 | Binop_f0 Binop_f

binop_rect :: (Binop_i -> a1) -> (Binop_f -> a1) -> Binop -> a1
binop_rect f f0 b =
  case b of {
   Binop_i0 x -> f x;
   Binop_f0 x -> f0 x}

binop_rec :: (Binop_i -> a1) -> (Binop_f -> a1) -> Binop -> a1
binop_rec =
  binop_rect

data Relop_i =
   ROI_eq
 | ROI_ne
 | ROI_lt Sx
 | ROI_gt Sx
 | ROI_le Sx
 | ROI_ge Sx

data Relop_f =
   ROF_eq
 | ROF_ne
 | ROF_lt
 | ROF_gt
 | ROF_le
 | ROF_ge

data Relop =
   Relop_i0 Relop_i
 | Relop_f0 Relop_f

relop_rect :: (Relop_i -> a1) -> (Relop_f -> a1) -> Relop -> a1
relop_rect f f0 r =
  case r of {
   Relop_i0 x -> f x;
   Relop_f0 x -> f0 x}

relop_rec :: (Relop_i -> a1) -> (Relop_f -> a1) -> Relop -> a1
relop_rec =
  relop_rect

data Cvtop =
   CVO_convert
 | CVO_reinterpret

data Basic_instruction =
   BI_unreachable
 | BI_nop
 | BI_drop
 | BI_select
 | BI_block Function_type (List Basic_instruction)
 | BI_loop Function_type (List Basic_instruction)
 | BI_if Function_type (List Basic_instruction) (List Basic_instruction)
 | BI_br Immediate
 | BI_br_if Immediate
 | BI_br_table (List Immediate) Immediate
 | BI_return
 | BI_call Immediate
 | BI_call_indirect Immediate
 | BI_get_local Immediate
 | BI_set_local Immediate
 | BI_tee_local Immediate
 | BI_get_global Immediate
 | BI_set_global Immediate
 | BI_load Value_type (Option (Prod Packed_type Sx)) Alignment_exponent 
 Static_offset
 | BI_store Value_type (Option Packed_type) Alignment_exponent Static_offset
 | BI_current_memory
 | BI_grow_memory
 | BI_const Value
 | BI_unop Value_type Unop
 | BI_binop Value_type Binop
 | BI_testop Value_type
 | BI_relop Value_type Relop
 | BI_cvtop Value_type Cvtop Value_type (Option Sx)

type Funcaddr = Immediate

type Tableaddr = Immediate

type Memaddr = Immediate

type Globaladdr = Immediate

data Instance =
   Build_instance (List Function_type) (List Funcaddr) (List Tableaddr) 
 (List Memaddr) (List Globaladdr)

inst_types :: Instance -> List Function_type
inst_types i =
  case i of {
   Build_instance inst_types0 _ _ _ _ -> inst_types0}

inst_tab :: Instance -> List Tableaddr
inst_tab i =
  case i of {
   Build_instance _ _ inst_tab0 _ _ -> inst_tab0}

inst_globs :: Instance -> List Globaladdr
inst_globs i =
  case i of {
   Build_instance _ _ _ _ inst_globs0 -> inst_globs0}

data Function_closure host_function =
   FC_func_native Instance Function_type (List Value_type) (List
                                                           Basic_instruction)
 | FC_func_host Function_type host_function

type Funcelem = Option Nat

data Tableinst =
   Build_tableinst (List Funcelem) (Option N)

table_data :: Tableinst -> List Funcelem
table_data t =
  case t of {
   Build_tableinst table_data0 _ -> table_data0}

data Global =
   Build_global Mutability Value

g_mut :: Global -> Mutability
g_mut g =
  case g of {
   Build_global g_mut0 _ -> g_mut0}

g_val :: Global -> Value
g_val g =
  case g of {
   Build_global _ g_val0 -> g_val0}

data Store_record host_function =
   Build_store_record (List (Function_closure host_function)) (List
                                                              Tableinst) 
 (List Memory) (List Global)

s_funcs :: (Store_record a1) -> List (Function_closure a1)
s_funcs s =
  case s of {
   Build_store_record s_funcs0 _ _ _ -> s_funcs0}

s_tables :: (Store_record a1) -> List Tableinst
s_tables s =
  case s of {
   Build_store_record _ s_tables0 _ _ -> s_tables0}

s_mems :: (Store_record a1) -> List Memory
s_mems s =
  case s of {
   Build_store_record _ _ s_mems0 _ -> s_mems0}

s_globals :: (Store_record a1) -> List Global
s_globals s =
  case s of {
   Build_store_record _ _ _ s_globals0 -> s_globals0}

data Frame =
   Build_frame (List Value) Instance

f_locs :: Frame -> List Value
f_locs f =
  case f of {
   Build_frame f_locs0 _ -> f_locs0}

f_inst :: Frame -> Instance
f_inst f =
  case f of {
   Build_frame _ f_inst0 -> f_inst0}

data Administrative_instruction =
   AI_basic Basic_instruction
 | AI_trap
 | AI_invoke Funcaddr
 | AI_label Nat (List Administrative_instruction) (List
                                                  Administrative_instruction)
 | AI_local Nat Frame (List Administrative_instruction)

data Lholed =
   LH_base (List Administrative_instruction) (List
                                             Administrative_instruction)
 | LH_rec (List Administrative_instruction) Nat (List
                                                Administrative_instruction) 
 Lholed (List Administrative_instruction)

type Config_tuple host_function =
  Prod (Prod (Store_record host_function) Frame)
  (List Administrative_instruction)

data Res_step =
   RS_crash
 | RS_break Nat (List Value)
 | RS_return (List Value)
 | RS_normal (List Administrative_instruction)

type Res_tuple host_function =
  Prod (Prod (Store_record host_function) Frame) Res_step

immediate_eqType :: Type
immediate_eqType =
  unsafeCoerce nat_eqMixin

funcaddr_eqType :: Type
funcaddr_eqType =
  unsafeCoerce nat_eqMixin

tableaddr_eqType :: Type
tableaddr_eqType =
  unsafeCoerce nat_eqMixin

memaddr_eqType :: Type
memaddr_eqType =
  unsafeCoerce nat_eqMixin

globaladdr_eqType :: Type
globaladdr_eqType =
  unsafeCoerce nat_eqMixin

value_type_beq :: Value_type -> Value_type -> Bool
value_type_beq x y =
  case x of {
   T_i32 -> case y of {
             T_i32 -> True;
             _ -> False};
   T_i64 -> case y of {
             T_i64 -> True;
             _ -> False};
   T_f32 -> case y of {
             T_f32 -> True;
             _ -> False};
   T_f64 -> case y of {
             T_f64 -> True;
             _ -> False}}

value_type_eq_dec :: Value_type -> Value_type -> Sumbool
value_type_eq_dec x y =
  let {b = value_type_beq x y} in case b of {
                                   True -> Left;
                                   False -> Right}

value_type_eqb :: Value_type -> Value_type -> Bool
value_type_eqb v1 v2 =
  is_left (value_type_eq_dec v1 v2)

eqvalue_typeP :: Axiom Value_type
eqvalue_typeP =
  eq_dec_Equality_axiom value_type_eq_dec

value_type_eqMixin :: Mixin_of Value_type
value_type_eqMixin =
  Mixin value_type_eqb eqvalue_typeP

value_type_eqType :: Type
value_type_eqType =
  unsafeCoerce value_type_eqMixin

packed_type_beq :: Packed_type -> Packed_type -> Bool
packed_type_beq x y =
  case x of {
   Tp_i8 -> case y of {
             Tp_i8 -> True;
             _ -> False};
   Tp_i16 -> case y of {
              Tp_i16 -> True;
              _ -> False};
   Tp_i32 -> case y of {
              Tp_i32 -> True;
              _ -> False}}

packed_type_eq_dec :: Packed_type -> Packed_type -> Sumbool
packed_type_eq_dec x y =
  let {b = packed_type_beq x y} in case b of {
                                    True -> Left;
                                    False -> Right}

packed_type_eqb :: Packed_type -> Packed_type -> Bool
packed_type_eqb v1 v2 =
  is_left (packed_type_eq_dec v1 v2)

eqpacked_typeP :: Axiom Packed_type
eqpacked_typeP =
  eq_dec_Equality_axiom packed_type_eq_dec

packed_type_eqMixin :: Mixin_of Packed_type
packed_type_eqMixin =
  Mixin packed_type_eqb eqpacked_typeP

packed_type_eqType :: Type
packed_type_eqType =
  unsafeCoerce packed_type_eqMixin

function_type_eq_dec :: Function_type -> Function_type -> Sumbool
function_type_eq_dec tf1 tf2 =
  function_type_rect (\r r0 x ->
    case x of {
     Tf r1 r2 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Left) (\_ -> Right)
          (eq_comparable (seq_eqType value_type_eqType) (unsafeCoerce r0)
            (unsafeCoerce r2))) (\_ -> Right)
        (eq_comparable (seq_eqType value_type_eqType) (unsafeCoerce r)
          (unsafeCoerce r1))}) tf1 tf2

function_type_eqb :: Function_type -> Function_type -> Bool
function_type_eqb v1 v2 =
  is_left (function_type_eq_dec v1 v2)

eqfunction_typeP :: Axiom Function_type
eqfunction_typeP =
  eq_dec_Equality_axiom function_type_eq_dec

function_type_eqMixin :: Mixin_of Function_type
function_type_eqMixin =
  Mixin function_type_eqb eqfunction_typeP

function_type_eqType :: Type
function_type_eqType =
  unsafeCoerce function_type_eqMixin

sx_beq :: Sx -> Sx -> Bool
sx_beq x y =
  case x of {
   SX_S -> case y of {
            SX_S -> True;
            SX_U -> False};
   SX_U -> case y of {
            SX_S -> False;
            SX_U -> True}}

sx_eq_dec :: Sx -> Sx -> Sumbool
sx_eq_dec x y =
  let {b = sx_beq x y} in case b of {
                           True -> Left;
                           False -> Right}

sx_eqb :: Sx -> Sx -> Bool
sx_eqb v1 v2 =
  is_left (sx_eq_dec v1 v2)

eqsxP :: Axiom Sx
eqsxP =
  eq_dec_Equality_axiom sx_eq_dec

sx_eqMixin :: Mixin_of Sx
sx_eqMixin =
  Mixin sx_eqb eqsxP

sx_eqType :: Type
sx_eqType =
  unsafeCoerce sx_eqMixin

unop_i_beq :: Unop_i -> Unop_i -> Bool
unop_i_beq x y =
  case x of {
   UOI_clz -> case y of {
               UOI_clz -> True;
               _ -> False};
   UOI_ctz -> case y of {
               UOI_ctz -> True;
               _ -> False};
   UOI_popcnt -> case y of {
                  UOI_popcnt -> True;
                  _ -> False}}

unop_i_eq_dec :: Unop_i -> Unop_i -> Sumbool
unop_i_eq_dec x y =
  let {b = unop_i_beq x y} in case b of {
                               True -> Left;
                               False -> Right}

unop_i_eqb :: Unop_i -> Unop_i -> Bool
unop_i_eqb v1 v2 =
  is_left (unop_i_eq_dec v1 v2)

equnop_iP :: Axiom Unop_i
equnop_iP =
  eq_dec_Equality_axiom unop_i_eq_dec

unop_i_eqMixin :: Mixin_of Unop_i
unop_i_eqMixin =
  Mixin unop_i_eqb equnop_iP

unop_i_eqType :: Type
unop_i_eqType =
  unsafeCoerce unop_i_eqMixin

unop_f_beq :: Unop_f -> Unop_f -> Bool
unop_f_beq x y =
  case x of {
   UOF_neg -> case y of {
               UOF_neg -> True;
               _ -> False};
   UOF_abs -> case y of {
               UOF_abs -> True;
               _ -> False};
   UOF_ceil -> case y of {
                UOF_ceil -> True;
                _ -> False};
   UOF_floor -> case y of {
                 UOF_floor -> True;
                 _ -> False};
   UOF_trunc -> case y of {
                 UOF_trunc -> True;
                 _ -> False};
   UOF_nearest -> case y of {
                   UOF_nearest -> True;
                   _ -> False};
   UOF_sqrt -> case y of {
                UOF_sqrt -> True;
                _ -> False}}

unop_f_eq_dec :: Unop_f -> Unop_f -> Sumbool
unop_f_eq_dec x y =
  let {b = unop_f_beq x y} in case b of {
                               True -> Left;
                               False -> Right}

unop_f_eqb :: Unop_f -> Unop_f -> Bool
unop_f_eqb v1 v2 =
  is_left (unop_f_eq_dec v1 v2)

equnop_fP :: Axiom Unop_f
equnop_fP =
  eq_dec_Equality_axiom unop_f_eq_dec

unop_f_eqMixin :: Mixin_of Unop_f
unop_f_eqMixin =
  Mixin unop_f_eqb equnop_fP

unop_f_eqType :: Type
unop_f_eqType =
  unsafeCoerce unop_f_eqMixin

binop_i_beq :: Binop_i -> Binop_i -> Bool
binop_i_beq x y =
  case x of {
   BOI_add -> case y of {
               BOI_add -> True;
               _ -> False};
   BOI_sub -> case y of {
               BOI_sub -> True;
               _ -> False};
   BOI_mul -> case y of {
               BOI_mul -> True;
               _ -> False};
   BOI_div x0 -> case y of {
                  BOI_div x1 -> sx_beq x0 x1;
                  _ -> False};
   BOI_rem x0 -> case y of {
                  BOI_rem x1 -> sx_beq x0 x1;
                  _ -> False};
   BOI_and -> case y of {
               BOI_and -> True;
               _ -> False};
   BOI_or -> case y of {
              BOI_or -> True;
              _ -> False};
   BOI_xor -> case y of {
               BOI_xor -> True;
               _ -> False};
   BOI_shl -> case y of {
               BOI_shl -> True;
               _ -> False};
   BOI_shr x0 -> case y of {
                  BOI_shr x1 -> sx_beq x0 x1;
                  _ -> False};
   BOI_rotl -> case y of {
                BOI_rotl -> True;
                _ -> False};
   BOI_rotr -> case y of {
                BOI_rotr -> True;
                _ -> False}}

binop_i_eq_dec :: Binop_i -> Binop_i -> Sumbool
binop_i_eq_dec x y =
  let {b = binop_i_beq x y} in case b of {
                                True -> Left;
                                False -> Right}

binop_i_eqb :: Binop_i -> Binop_i -> Bool
binop_i_eqb v1 v2 =
  is_left (binop_i_eq_dec v1 v2)

eqbinop_iP :: Axiom Binop_i
eqbinop_iP =
  eq_dec_Equality_axiom binop_i_eq_dec

binop_i_eqMixin :: Mixin_of Binop_i
binop_i_eqMixin =
  Mixin binop_i_eqb eqbinop_iP

binop_i_eqType :: Type
binop_i_eqType =
  unsafeCoerce binop_i_eqMixin

binop_f_beq :: Binop_f -> Binop_f -> Bool
binop_f_beq x y =
  case x of {
   BOF_add -> case y of {
               BOF_add -> True;
               _ -> False};
   BOF_sub -> case y of {
               BOF_sub -> True;
               _ -> False};
   BOF_mul -> case y of {
               BOF_mul -> True;
               _ -> False};
   BOF_div -> case y of {
               BOF_div -> True;
               _ -> False};
   BOF_min -> case y of {
               BOF_min -> True;
               _ -> False};
   BOF_max -> case y of {
               BOF_max -> True;
               _ -> False};
   BOF_copysign -> case y of {
                    BOF_copysign -> True;
                    _ -> False}}

binop_f_eq_dec :: Binop_f -> Binop_f -> Sumbool
binop_f_eq_dec x y =
  let {b = binop_f_beq x y} in case b of {
                                True -> Left;
                                False -> Right}

binop_f_eqb :: Binop_f -> Binop_f -> Bool
binop_f_eqb v1 v2 =
  is_left (binop_f_eq_dec v1 v2)

eqbinop_fP :: Axiom Binop_f
eqbinop_fP =
  eq_dec_Equality_axiom binop_f_eq_dec

binop_f_eqMixin :: Mixin_of Binop_f
binop_f_eqMixin =
  Mixin binop_f_eqb eqbinop_fP

binop_f_eqType :: Type
binop_f_eqType =
  unsafeCoerce binop_f_eqMixin

testop_beq :: Bool
testop_beq =
  True

testop_eq_dec :: Sumbool
testop_eq_dec =
  case testop_beq of {
   True -> Left;
   False -> Right}

testop_eqb :: Bool
testop_eqb =
  is_left testop_eq_dec

eqtestopP :: Reflect
eqtestopP =
  eq_dec_Equality_axiom (\_ _ -> testop_eq_dec) __ __

testop_eqMixin :: Mixin_of ()
testop_eqMixin =
  Mixin (\_ _ -> testop_eqb) (\_ _ -> eqtestopP)

testop_eqType :: Type
testop_eqType =
  unsafeCoerce testop_eqMixin

relop_i_beq :: Relop_i -> Relop_i -> Bool
relop_i_beq x y =
  case x of {
   ROI_eq -> case y of {
              ROI_eq -> True;
              _ -> False};
   ROI_ne -> case y of {
              ROI_ne -> True;
              _ -> False};
   ROI_lt x0 -> case y of {
                 ROI_lt x1 -> sx_beq x0 x1;
                 _ -> False};
   ROI_gt x0 -> case y of {
                 ROI_gt x1 -> sx_beq x0 x1;
                 _ -> False};
   ROI_le x0 -> case y of {
                 ROI_le x1 -> sx_beq x0 x1;
                 _ -> False};
   ROI_ge x0 -> case y of {
                 ROI_ge x1 -> sx_beq x0 x1;
                 _ -> False}}

relop_i_eq_dec :: Relop_i -> Relop_i -> Sumbool
relop_i_eq_dec x y =
  let {b = relop_i_beq x y} in case b of {
                                True -> Left;
                                False -> Right}

relop_i_eqb :: Relop_i -> Relop_i -> Bool
relop_i_eqb v1 v2 =
  is_left (relop_i_eq_dec v1 v2)

eqrelop_iP :: Axiom Relop_i
eqrelop_iP =
  eq_dec_Equality_axiom relop_i_eq_dec

relop_i_eqMixin :: Mixin_of Relop_i
relop_i_eqMixin =
  Mixin relop_i_eqb eqrelop_iP

relop_i_eqType :: Type
relop_i_eqType =
  unsafeCoerce relop_i_eqMixin

relop_f_beq :: Relop_f -> Relop_f -> Bool
relop_f_beq x y =
  case x of {
   ROF_eq -> case y of {
              ROF_eq -> True;
              _ -> False};
   ROF_ne -> case y of {
              ROF_ne -> True;
              _ -> False};
   ROF_lt -> case y of {
              ROF_lt -> True;
              _ -> False};
   ROF_gt -> case y of {
              ROF_gt -> True;
              _ -> False};
   ROF_le -> case y of {
              ROF_le -> True;
              _ -> False};
   ROF_ge -> case y of {
              ROF_ge -> True;
              _ -> False}}

relop_f_eq_dec :: Relop_f -> Relop_f -> Sumbool
relop_f_eq_dec x y =
  let {b = relop_f_beq x y} in case b of {
                                True -> Left;
                                False -> Right}

relop_f_eqb :: Relop_f -> Relop_f -> Bool
relop_f_eqb v1 v2 =
  is_left (relop_f_eq_dec v1 v2)

eqrelop_fP :: Axiom Relop_f
eqrelop_fP =
  eq_dec_Equality_axiom relop_f_eq_dec

relop_f_eqMixin :: Mixin_of Relop_f
relop_f_eqMixin =
  Mixin relop_f_eqb eqrelop_fP

relop_f_eqType :: Type
relop_f_eqType =
  unsafeCoerce relop_f_eqMixin

cvtop_beq :: Cvtop -> Cvtop -> Bool
cvtop_beq x y =
  case x of {
   CVO_convert -> case y of {
                   CVO_convert -> True;
                   CVO_reinterpret -> False};
   CVO_reinterpret ->
    case y of {
     CVO_convert -> False;
     CVO_reinterpret -> True}}

cvtop_eq_dec :: Cvtop -> Cvtop -> Sumbool
cvtop_eq_dec x y =
  let {b = cvtop_beq x y} in case b of {
                              True -> Left;
                              False -> Right}

cvtop_eqb :: Cvtop -> Cvtop -> Bool
cvtop_eqb v1 v2 =
  is_left (cvtop_eq_dec v1 v2)

eqcvtopP :: Axiom Cvtop
eqcvtopP =
  eq_dec_Equality_axiom cvtop_eq_dec

cvtop_eqMixin :: Mixin_of Cvtop
cvtop_eqMixin =
  Mixin cvtop_eqb eqcvtopP

cvtop_eqType :: Type
cvtop_eqType =
  unsafeCoerce cvtop_eqMixin

value_eq_dec :: Value -> Value -> Sumbool
value_eq_dec v1 v2 =
  value_rect (\s x ->
    case x of {
     VAL_int32 s0 ->
      sumbool_rec (\_ -> Left) (\_ -> Right) (eq_comparable i32 s s0);
     _ -> Right}) (\s x ->
    case x of {
     VAL_int64 s0 ->
      sumbool_rec (\_ -> Left) (\_ -> Right) (eq_comparable i64 s s0);
     _ -> Right}) (\s x ->
    case x of {
     VAL_float32 s0 ->
      sumbool_rec (\_ -> Left) (\_ -> Right) (eq_comparable f32 s s0);
     _ -> Right}) (\s x ->
    case x of {
     VAL_float64 s0 ->
      sumbool_rec (\_ -> Left) (\_ -> Right) (eq_comparable f64 s s0);
     _ -> Right}) v1 v2

value_eqb :: Value -> Value -> Bool
value_eqb v1 v2 =
  is_left (value_eq_dec v1 v2)

eqvalueP :: Axiom Value
eqvalueP =
  eq_dec_Equality_axiom value_eq_dec

value_eqMixin :: Mixin_of Value
value_eqMixin =
  Mixin value_eqb eqvalueP

value_eqType :: Type
value_eqType =
  unsafeCoerce value_eqMixin

basic_instruction_rect' :: a1 -> a1 -> a1 -> a1 -> (Function_type -> (List
                           Basic_instruction) -> (Forall Basic_instruction
                           a1) -> a1) -> (Function_type -> (List
                           Basic_instruction) -> (Forall Basic_instruction
                           a1) -> a1) -> (Function_type -> (List
                           Basic_instruction) -> (List Basic_instruction) ->
                           (Forall Basic_instruction a1) -> (Forall
                           Basic_instruction a1) -> a1) -> (Immediate -> a1)
                           -> (Immediate -> a1) -> ((List Immediate) ->
                           Immediate -> a1) -> a1 -> (Immediate -> a1) ->
                           (Immediate -> a1) -> (Immediate -> a1) ->
                           (Immediate -> a1) -> (Immediate -> a1) ->
                           (Immediate -> a1) -> (Immediate -> a1) ->
                           (Value_type -> (Option (Prod Packed_type Sx)) ->
                           Alignment_exponent -> Static_offset -> a1) ->
                           (Value_type -> (Option Packed_type) ->
                           Alignment_exponent -> Static_offset -> a1) -> a1
                           -> a1 -> (Value -> a1) -> (Value_type -> Unop ->
                           a1) -> (Value_type -> Binop -> a1) -> (Value_type
                           -> () -> a1) -> (Value_type -> Relop -> a1) ->
                           (Value_type -> Cvtop -> Value_type -> (Option 
                           Sx) -> a1) -> Basic_instruction -> a1
basic_instruction_rect' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 =
  let {
   rect_list = let {
                rect_list es =
                  case es of {
                   Nil -> Forall_nil;
                   Cons e l -> Forall_cons e l
                    (basic_instruction_rect' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
                      x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                      x24 x25 x26 e) (rect_list l)}}
               in rect_list}
  in
  (\__top_assumption_ ->
  let {
   _evar_0_ = \f l -> let {_rect_list_ = rect_list l} in x3 f l _rect_list_}
  in
  let {
   _evar_0_0 = \f l -> let {_rect_list_ = rect_list l} in x4 f l _rect_list_}
  in
  let {
   _evar_0_1 = \f l l0 ->
    let {_rect_list_ = rect_list l0} in
    let {_rect_list1_ = rect_list l} in x5 f l l0 _rect_list1_ _rect_list_}
  in
  case __top_assumption_ of {
   BI_unreachable -> x;
   BI_nop -> x0;
   BI_drop -> x1;
   BI_select -> x2;
   BI_block x27 x28 -> _evar_0_ x27 x28;
   BI_loop x27 x28 -> _evar_0_0 x27 x28;
   BI_if x27 x28 x29 -> _evar_0_1 x27 x28 x29;
   BI_br x27 -> x6 x27;
   BI_br_if x27 -> x7 x27;
   BI_br_table x27 x28 -> x8 x27 x28;
   BI_return -> x9;
   BI_call x27 -> x10 x27;
   BI_call_indirect x27 -> x11 x27;
   BI_get_local x27 -> x12 x27;
   BI_set_local x27 -> x13 x27;
   BI_tee_local x27 -> x14 x27;
   BI_get_global x27 -> x15 x27;
   BI_set_global x27 -> x16 x27;
   BI_load x27 x28 x29 x30 -> x17 x27 x28 x29 x30;
   BI_store x27 x28 x29 x30 -> x18 x27 x28 x29 x30;
   BI_current_memory -> x19;
   BI_grow_memory -> x20;
   BI_const x27 -> x21 x27;
   BI_unop x27 x28 -> x22 x27 x28;
   BI_binop x27 x28 -> x23 x27 x28;
   BI_testop x27 -> x24 x27 __;
   BI_relop x27 x28 -> x25 x27 x28;
   BI_cvtop x27 x28 x29 x30 -> x26 x27 x28 x29 x30})

basic_instruction_eq_dec :: Basic_instruction -> Basic_instruction -> Sumbool
basic_instruction_eq_dec x =
  basic_instruction_rect' (\y ->
    case y of {
     BI_unreachable -> Left;
     _ -> Right}) (\y -> case y of {
                          BI_nop -> Left;
                          _ -> Right}) (\y ->
    case y of {
     BI_drop -> Left;
     _ -> Right}) (\y -> case y of {
                          BI_select -> Left;
                          _ -> Right}) (\f l x0 y ->
    case y of {
     BI_block f0 l0 ->
      let {decide = forall_forall_eq_dec l l0 x0} in
      let {
       decide0 = eq_comparable function_type_eqType (unsafeCoerce f)
                   (unsafeCoerce f0)}
      in
      case decide0 of {
       Left ->
        let {
         _evar_0_ = case decide of {
                     Left -> let {_evar_0_ = Left} in eq_rec_r l0 _evar_0_ l;
                     Right -> Right}}
        in
        eq_rec_r f0 _evar_0_ f;
       Right -> Right};
     _ -> Right}) (\f l x0 y ->
    case y of {
     BI_loop f0 l0 ->
      let {decide = forall_forall_eq_dec l l0 x0} in
      let {
       decide0 = eq_comparable function_type_eqType (unsafeCoerce f)
                   (unsafeCoerce f0)}
      in
      case decide0 of {
       Left ->
        let {
         _evar_0_ = case decide of {
                     Left -> let {_evar_0_ = Left} in eq_rec_r l0 _evar_0_ l;
                     Right -> Right}}
        in
        eq_rec_r f0 _evar_0_ f;
       Right -> Right};
     _ -> Right}) (\f l l0 x0 x1 y ->
    case y of {
     BI_if f0 l1 l2 ->
      let {decide = forall_forall_eq_dec l0 l2 x1} in
      let {decide0 = forall_forall_eq_dec l l1 x0} in
      let {
       decide1 = eq_comparable function_type_eqType (unsafeCoerce f)
                   (unsafeCoerce f0)}
      in
      case decide1 of {
       Left ->
        let {
         _evar_0_ = case decide0 of {
                     Left ->
                      let {
                       _evar_0_ = case decide of {
                                   Left ->
                                    let {_evar_0_ = Left} in
                                    eq_rec_r l2 _evar_0_ l0;
                                   Right -> Right}}
                      in
                      eq_rec_r l1 _evar_0_ l;
                     Right -> Right}}
        in
        eq_rec_r f0 _evar_0_ f;
       Right -> Right};
     _ -> Right}) (\i y ->
    case y of {
     BI_br i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\i y ->
    case y of {
     BI_br_if i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\l i y ->
    case y of {
     BI_br_table l0 i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      let {
       decide0 = eq_comparable (seq_eqType immediate_eqType) (unsafeCoerce l)
                   (unsafeCoerce l0)}
      in
      case decide0 of {
       Left ->
        let {
         _evar_0_ = case decide of {
                     Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
                     Right -> Right}}
        in
        eq_rec_r l0 _evar_0_ l;
       Right -> Right};
     _ -> Right}) (\y -> case y of {
                          BI_return -> Left;
                          _ -> Right}) (\i y ->
    case y of {
     BI_call i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\i y ->
    case y of {
     BI_call_indirect i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\i y ->
    case y of {
     BI_get_local i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\i y ->
    case y of {
     BI_set_local i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\i y ->
    case y of {
     BI_tee_local i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\i y ->
    case y of {
     BI_get_global i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\i y ->
    case y of {
     BI_set_global i0 ->
      let {
       decide = eq_comparable immediate_eqType (unsafeCoerce i)
                  (unsafeCoerce i0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r i0 _evar_0_ i;
       Right -> Right};
     _ -> Right}) (\v o a s y ->
    case y of {
     BI_load v0 o0 a0 s0 ->
      let {
       decide = eq_comparable bin_nat_eqType (unsafeCoerce s)
                  (unsafeCoerce s0)}
      in
      let {
       decide0 = eq_comparable bin_nat_eqType (unsafeCoerce a)
                   (unsafeCoerce a0)}
      in
      let {
       decide1 = eq_comparable
                   (option_eqType (prod_eqType packed_type_eqType sx_eqType))
                   (unsafeCoerce o) (unsafeCoerce o0)}
      in
      let {
       decide2 = eq_comparable value_type_eqType (unsafeCoerce v)
                   (unsafeCoerce v0)}
      in
      case decide2 of {
       Left ->
        let {
         _evar_0_ = case decide1 of {
                     Left ->
                      let {
                       _evar_0_ = case decide0 of {
                                   Left ->
                                    let {
                                     _evar_0_ = case decide of {
                                                 Left ->
                                                  let {_evar_0_ = Left} in
                                                  eq_rec_r s0 _evar_0_ s;
                                                 Right -> Right}}
                                    in
                                    eq_rec_r a0 _evar_0_ a;
                                   Right -> Right}}
                      in
                      eq_rec_r o0 _evar_0_ o;
                     Right -> Right}}
        in
        eq_rec_r v0 _evar_0_ v;
       Right -> Right};
     _ -> Right}) (\v o a s y ->
    case y of {
     BI_store v0 o0 a0 s0 ->
      let {
       decide = eq_comparable bin_nat_eqType (unsafeCoerce s)
                  (unsafeCoerce s0)}
      in
      let {
       decide0 = eq_comparable bin_nat_eqType (unsafeCoerce a)
                   (unsafeCoerce a0)}
      in
      let {
       decide1 = eq_comparable (option_eqType packed_type_eqType)
                   (unsafeCoerce o) (unsafeCoerce o0)}
      in
      let {
       decide2 = eq_comparable value_type_eqType (unsafeCoerce v)
                   (unsafeCoerce v0)}
      in
      case decide2 of {
       Left ->
        let {
         _evar_0_ = case decide1 of {
                     Left ->
                      let {
                       _evar_0_ = case decide0 of {
                                   Left ->
                                    let {
                                     _evar_0_ = case decide of {
                                                 Left ->
                                                  let {_evar_0_ = Left} in
                                                  eq_rec_r s0 _evar_0_ s;
                                                 Right -> Right}}
                                    in
                                    eq_rec_r a0 _evar_0_ a;
                                   Right -> Right}}
                      in
                      eq_rec_r o0 _evar_0_ o;
                     Right -> Right}}
        in
        eq_rec_r v0 _evar_0_ v;
       Right -> Right};
     _ -> Right}) (\y -> case y of {
                          BI_current_memory -> Left;
                          _ -> Right}) (\y ->
    case y of {
     BI_grow_memory -> Left;
     _ -> Right}) (\v y ->
    case y of {
     BI_const v0 ->
      let {
       decide = eq_comparable value_eqType (unsafeCoerce v) (unsafeCoerce v0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r v0 _evar_0_ v;
       Right -> Right};
     _ -> Right}) (\v u y ->
    case y of {
     BI_unop v0 u0 ->
      let {
       decide = unop_rec (\u1 x0 ->
                  case x0 of {
                   Unop_i0 u2 ->
                    sumbool_rec (\_ -> Left) (\_ -> Right)
                      (eq_comparable unop_i_eqType (unsafeCoerce u1)
                        (unsafeCoerce u2));
                   Unop_f0 _ -> Right}) (\u1 x0 ->
                  case x0 of {
                   Unop_i0 _ -> Right;
                   Unop_f0 u2 ->
                    sumbool_rec (\_ -> Left) (\_ -> Right)
                      (eq_comparable unop_f_eqType (unsafeCoerce u1)
                        (unsafeCoerce u2))}) u u0}
      in
      let {
       decide0 = eq_comparable value_type_eqType (unsafeCoerce v)
                   (unsafeCoerce v0)}
      in
      case decide0 of {
       Left ->
        let {
         _evar_0_ = case decide of {
                     Left -> let {_evar_0_ = Left} in eq_rec_r u0 _evar_0_ u;
                     Right -> Right}}
        in
        eq_rec_r v0 _evar_0_ v;
       Right -> Right};
     _ -> Right}) (\v b y ->
    case y of {
     BI_binop v0 b0 ->
      let {
       decide = binop_rec (\b1 x0 ->
                  case x0 of {
                   Binop_i0 b2 ->
                    sumbool_rec (\_ -> Left) (\_ -> Right)
                      (eq_comparable binop_i_eqType (unsafeCoerce b1)
                        (unsafeCoerce b2));
                   Binop_f0 _ -> Right}) (\b1 x0 ->
                  case x0 of {
                   Binop_i0 _ -> Right;
                   Binop_f0 b2 ->
                    sumbool_rec (\_ -> Left) (\_ -> Right)
                      (eq_comparable binop_f_eqType (unsafeCoerce b1)
                        (unsafeCoerce b2))}) b b0}
      in
      let {
       decide0 = eq_comparable value_type_eqType (unsafeCoerce v)
                   (unsafeCoerce v0)}
      in
      case decide0 of {
       Left ->
        let {
         _evar_0_ = case decide of {
                     Left -> let {_evar_0_ = Left} in eq_rec_r b0 _evar_0_ b;
                     Right -> Right}}
        in
        eq_rec_r v0 _evar_0_ v;
       Right -> Right};
     _ -> Right}) (\v _ y ->
    case y of {
     BI_testop v0 ->
      let {decide = eq_comparable testop_eqType __ __} in
      let {
       decide0 = eq_comparable value_type_eqType (unsafeCoerce v)
                   (unsafeCoerce v0)}
      in
      case decide0 of {
       Left ->
        let {
         _evar_0_ = case decide of {
                     Left -> let {_evar_0_ = Left} in eq_rec_r __ _evar_0_ __;
                     Right -> Right}}
        in
        eq_rec_r v0 _evar_0_ v;
       Right -> Right};
     _ -> Right}) (\v r y ->
    case y of {
     BI_relop v0 r0 ->
      let {
       decide = relop_rec (\r1 x0 ->
                  case x0 of {
                   Relop_i0 r2 ->
                    sumbool_rec (\_ -> Left) (\_ -> Right)
                      (eq_comparable relop_i_eqType (unsafeCoerce r1)
                        (unsafeCoerce r2));
                   Relop_f0 _ -> Right}) (\r1 x0 ->
                  case x0 of {
                   Relop_i0 _ -> Right;
                   Relop_f0 r2 ->
                    sumbool_rec (\_ -> Left) (\_ -> Right)
                      (eq_comparable relop_f_eqType (unsafeCoerce r1)
                        (unsafeCoerce r2))}) r r0}
      in
      let {
       decide0 = eq_comparable value_type_eqType (unsafeCoerce v)
                   (unsafeCoerce v0)}
      in
      case decide0 of {
       Left ->
        let {
         _evar_0_ = case decide of {
                     Left -> let {_evar_0_ = Left} in eq_rec_r r0 _evar_0_ r;
                     Right -> Right}}
        in
        eq_rec_r v0 _evar_0_ v;
       Right -> Right};
     _ -> Right}) (\v c v0 o y ->
    case y of {
     BI_cvtop v1 c0 v2 o0 ->
      let {
       decide = eq_comparable (option_eqType sx_eqType) (unsafeCoerce o)
                  (unsafeCoerce o0)}
      in
      let {
       decide0 = eq_comparable value_type_eqType (unsafeCoerce v0)
                   (unsafeCoerce v2)}
      in
      let {
       decide1 = eq_comparable cvtop_eqType (unsafeCoerce c)
                   (unsafeCoerce c0)}
      in
      let {
       decide2 = eq_comparable value_type_eqType (unsafeCoerce v)
                   (unsafeCoerce v1)}
      in
      case decide2 of {
       Left ->
        let {
         _evar_0_ = case decide1 of {
                     Left ->
                      let {
                       _evar_0_ = case decide0 of {
                                   Left ->
                                    let {
                                     _evar_0_ = case decide of {
                                                 Left ->
                                                  let {_evar_0_ = Left} in
                                                  eq_rec_r o0 _evar_0_ o;
                                                 Right -> Right}}
                                    in
                                    eq_rec_r v2 _evar_0_ v0;
                                   Right -> Right}}
                      in
                      eq_rec_r c0 _evar_0_ c;
                     Right -> Right}}
        in
        eq_rec_r v1 _evar_0_ v;
       Right -> Right};
     _ -> Right}) x

basic_instruction_eqb :: Basic_instruction -> Basic_instruction -> Bool
basic_instruction_eqb cl1 cl2 =
  is_left (basic_instruction_eq_dec cl1 cl2)

eqbasic_instructionP :: Axiom Basic_instruction
eqbasic_instructionP =
  eq_dec_Equality_axiom basic_instruction_eq_dec

basic_instruction_eqMixin :: Mixin_of Basic_instruction
basic_instruction_eqMixin =
  Mixin basic_instruction_eqb eqbasic_instructionP

basic_instruction_eqType :: Type
basic_instruction_eqType =
  unsafeCoerce basic_instruction_eqMixin

instance_eq_dec :: Instance -> Instance -> Sumbool
instance_eq_dec i1 i2 =
  case i1 of {
   Build_instance inst_types0 inst_funcs inst_tab0 inst_memory inst_globs0 ->
    case i2 of {
     Build_instance inst_types1 inst_funcs0 inst_tab1 inst_memory0
      inst_globs1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ -> Left) (\_ -> Right)
                (eq_comparable (seq_eqType globaladdr_eqType)
                  (unsafeCoerce inst_globs0) (unsafeCoerce inst_globs1)))
              (\_ -> Right)
              (eq_comparable (seq_eqType memaddr_eqType)
                (unsafeCoerce inst_memory) (unsafeCoerce inst_memory0)))
            (\_ -> Right)
            (eq_comparable (seq_eqType tableaddr_eqType)
              (unsafeCoerce inst_tab0) (unsafeCoerce inst_tab1))) (\_ ->
          Right)
          (eq_comparable (seq_eqType funcaddr_eqType)
            (unsafeCoerce inst_funcs) (unsafeCoerce inst_funcs0))) (\_ ->
        Right)
        (eq_comparable (seq_eqType function_type_eqType)
          (unsafeCoerce inst_types0) (unsafeCoerce inst_types1))}}

instance_eqb :: Instance -> Instance -> Bool
instance_eqb i1 i2 =
  is_left (instance_eq_dec i1 i2)

eqinstanceP :: Axiom Instance
eqinstanceP =
  eq_dec_Equality_axiom instance_eq_dec

instance_eqMixin :: Mixin_of Instance
instance_eqMixin =
  Mixin instance_eqb eqinstanceP

instance_eqType :: Type
instance_eqType =
  unsafeCoerce instance_eqMixin

frame_eq_dec :: Frame -> Frame -> Sumbool
frame_eq_dec v1 v2 =
  case v1 of {
   Build_frame f_locs0 f_inst0 ->
    case v2 of {
     Build_frame f_locs1 f_inst1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Left) (\_ -> Right)
          (eq_comparable instance_eqType (unsafeCoerce f_inst0)
            (unsafeCoerce f_inst1))) (\_ -> Right)
        (eq_comparable (seq_eqType value_eqType) (unsafeCoerce f_locs0)
          (unsafeCoerce f_locs1))}}

frame_eqb :: Frame -> Frame -> Bool
frame_eqb v1 v2 =
  is_left (frame_eq_dec v1 v2)

eqframeP :: Axiom Frame
eqframeP =
  eq_dec_Equality_axiom frame_eq_dec

frame_eqMixin :: Mixin_of Frame
frame_eqMixin =
  Mixin frame_eqb eqframeP

frame_eqType :: Type
frame_eqType =
  unsafeCoerce frame_eqMixin

administrative_instruction_rect' :: (Basic_instruction -> a1) -> a1 ->
                                    (Funcaddr -> a1) -> (Nat -> (List
                                    Administrative_instruction) -> (List
                                    Administrative_instruction) -> (Forall
                                    Administrative_instruction a1) -> (Forall
                                    Administrative_instruction a1) -> a1) ->
                                    (Nat -> Frame -> (List
                                    Administrative_instruction) -> (Forall
                                    Administrative_instruction a1) -> a1) ->
                                    Administrative_instruction -> a1
administrative_instruction_rect' x x0 x1 x2 x3 =
  let {
   rect_list = let {
                rect_list es =
                  case es of {
                   Nil -> Forall_nil;
                   Cons e l -> Forall_cons e l
                    (administrative_instruction_rect' x x0 x1 x2 x3 e)
                    (rect_list l)}}
               in rect_list}
  in
  (\__top_assumption_ ->
  let {
   _evar_0_ = \n l l0 ->
    let {_rect_list_ = rect_list l0} in
    let {_rect_list1_ = rect_list l} in x2 n l l0 _rect_list1_ _rect_list_}
  in
  let {
   _evar_0_0 = \n f l ->
    let {_rect_list_ = rect_list l} in x3 n f l _rect_list_}
  in
  case __top_assumption_ of {
   AI_basic x4 -> x x4;
   AI_trap -> x0;
   AI_invoke x4 -> x1 x4;
   AI_label x4 x5 x6 -> _evar_0_ x4 x5 x6;
   AI_local x4 x5 x6 -> _evar_0_0 x4 x5 x6})

seq_administrative_instruction_rect' :: (Basic_instruction -> a1) -> a1 ->
                                        (Funcaddr -> a1) -> (Nat -> (List
                                        Administrative_instruction) -> (List
                                        Administrative_instruction) ->
                                        (Forall Administrative_instruction
                                        a1) -> (Forall
                                        Administrative_instruction a1) -> a1)
                                        -> (Nat -> Frame -> (List
                                        Administrative_instruction) ->
                                        (Forall Administrative_instruction
                                        a1) -> a1) -> (List
                                        Administrative_instruction) -> Forall
                                        Administrative_instruction a1
seq_administrative_instruction_rect' x x0 x1 x2 x3 l0 =
  list_rect Forall_nil (\a l1 iHl0 -> Forall_cons a l1
    (let {
      rect =
        let {
         rect_list = let {
                      rect_list es =
                        case es of {
                         Nil -> Forall_nil;
                         Cons e l -> Forall_cons e l (rect e) (rect_list l)}}
                     in rect_list}
        in
        (\__top_assumption_ ->
        let {
         _evar_0_ = \n l l2 ->
          let {_rect_list_ = rect_list l2} in
          let {_rect_list1_ = rect_list l} in
          x2 n l l2 _rect_list1_ _rect_list_}
        in
        let {
         _evar_0_0 = \n f l ->
          let {_rect_list_ = rect_list l} in x3 n f l _rect_list_}
        in
        case __top_assumption_ of {
         AI_basic x4 -> x x4;
         AI_trap -> x0;
         AI_invoke x4 -> x1 x4;
         AI_label x4 x5 x6 -> _evar_0_ x4 x5 x6;
         AI_local x4 x5 x6 -> _evar_0_0 x4 x5 x6})}
     in rect a) iHl0) l0

administrative_instruction_eq_dec :: Administrative_instruction ->
                                     Administrative_instruction -> Sumbool
administrative_instruction_eq_dec x =
  administrative_instruction_rect' (\b y ->
    case y of {
     AI_basic b0 ->
      let {
       decide = eq_comparable basic_instruction_eqType (unsafeCoerce b)
                  (unsafeCoerce b0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r b0 _evar_0_ b;
       Right -> Right};
     _ -> Right}) (\y -> case y of {
                          AI_trap -> Left;
                          _ -> Right}) (\f y ->
    case y of {
     AI_invoke f0 ->
      let {
       decide = eq_comparable funcaddr_eqType (unsafeCoerce f)
                  (unsafeCoerce f0)}
      in
      case decide of {
       Left -> let {_evar_0_ = Left} in eq_rec_r f0 _evar_0_ f;
       Right -> Right};
     _ -> Right}) (\n l l0 x0 x1 y ->
    case y of {
     AI_label n0 l1 l2 ->
      let {decide = forall_forall_eq_dec l0 l2 x1} in
      let {decide0 = forall_forall_eq_dec l l1 x0} in
      let {
       decide1 = eq_comparable nat_eqType (unsafeCoerce n) (unsafeCoerce n0)}
      in
      case decide1 of {
       Left ->
        let {
         _evar_0_ = case decide0 of {
                     Left ->
                      let {
                       _evar_0_ = case decide of {
                                   Left ->
                                    let {_evar_0_ = Left} in
                                    eq_rec_r l2 _evar_0_ l0;
                                   Right -> Right}}
                      in
                      eq_rec_r l1 _evar_0_ l;
                     Right -> Right}}
        in
        eq_rec_r n0 _evar_0_ n;
       Right -> Right};
     _ -> Right}) (\n f l x0 y ->
    case y of {
     AI_local n0 f0 l0 ->
      let {decide = forall_forall_eq_dec l l0 x0} in
      let {
       decide0 = eq_comparable frame_eqType (unsafeCoerce f)
                   (unsafeCoerce f0)}
      in
      let {
       decide1 = eq_comparable nat_eqType (unsafeCoerce n) (unsafeCoerce n0)}
      in
      case decide1 of {
       Left ->
        let {
         _evar_0_ = case decide0 of {
                     Left ->
                      let {
                       _evar_0_ = case decide of {
                                   Left ->
                                    let {_evar_0_ = Left} in
                                    eq_rec_r l0 _evar_0_ l;
                                   Right -> Right}}
                      in
                      eq_rec_r f0 _evar_0_ f;
                     Right -> Right}}
        in
        eq_rec_r n0 _evar_0_ n;
       Right -> Right};
     _ -> Right}) x

administrative_instruction_eqb :: Administrative_instruction ->
                                  Administrative_instruction -> Bool
administrative_instruction_eqb cl1 cl2 =
  is_left (administrative_instruction_eq_dec cl1 cl2)

eqadministrative_instructionP :: Axiom Administrative_instruction
eqadministrative_instructionP =
  eq_dec_Equality_axiom administrative_instruction_eq_dec

administrative_instruction_eqMixin :: Mixin_of Administrative_instruction
administrative_instruction_eqMixin =
  Mixin administrative_instruction_eqb eqadministrative_instructionP

administrative_instruction_eqType :: Type
administrative_instruction_eqType =
  unsafeCoerce administrative_instruction_eqMixin

type Functor f =
  () -> () -> (Any -> Any) -> f -> f
  -- singleton inductive, whose constructor was Build_Functor
  
data Monad m =
   Build_Monad (() -> Any -> m) (() -> () -> m -> (Any -> m) -> m)

ret :: (Monad a1) -> a2 -> a1
ret monad x =
  case monad of {
   Build_Monad ret0 _ -> unsafeCoerce ret0 __ x}

bind0 :: (Monad a1) -> a1 -> (a2 -> a1) -> a1
bind0 monad x x0 =
  case monad of {
   Build_Monad _ bind1 -> unsafeCoerce bind1 __ __ x x0}

liftM :: (Monad a1) -> (a2 -> a3) -> a1 -> a1
liftM m f x =
  bind0 m x (\x0 -> ret m (f x0))

functor_Monad :: (Monad a1) -> Functor a1
functor_Monad m _ _ =
  liftM m

those_aux :: (Option (List a1)) -> (List (Option a1)) -> Option (List a1)
those_aux acc l =
  case acc of {
   Some ys_rev ->
    case l of {
     Nil -> Some ys_rev;
     Cons o xs ->
      case o of {
       Some y -> those_aux (Some (Cons y ys_rev)) xs;
       None -> None}};
   None -> None}

those :: (List (Option a1)) -> Option (List a1)
those l =
  case those_aux (Some Nil) l of {
   Some l0 -> Some (rev l0);
   None -> None}

fold_lefti :: (Nat -> a1 -> a2 -> a1) -> (List a2) -> a1 -> a1
fold_lefti f xs acc0 =
  case fold_left (\pat x ->
         case pat of {
          Pair k acc -> Pair (add k (S O)) (f k acc x)}) xs (Pair O acc0) of {
   Pair _ acc_end -> acc_end}

read_bytes :: Memory -> N -> Nat -> Option Bytes
read_bytes m start_idx len =
  those
    (map (\off ->
      let {idx = add1 start_idx (of_nat off)} in mem_lookup idx (mem_data m))
      (iota O len))

write_bytes :: Memory -> N -> Bytes -> Option Memory
write_bytes m start_idx bs =
  let {
   x = fold_lefti (\off dat_o b ->
         case dat_o of {
          Some dat ->
           let {idx = add1 start_idx (of_nat off)} in mem_update idx b dat;
          None -> None}) bs (Some (mem_data m))}
  in
  case x of {
   Some dat -> Some (Build_memory dat (mem_max_opt m));
   None -> None}

upd_s_mem :: Type -> (Store_record Sort) -> (List Memory) -> Store_record
             Sort
upd_s_mem _ s m =
  Build_store_record (s_funcs s) (s_tables s) m (s_globals s)

page_size :: N
page_size =
  mul0 (Npos (XO (XO (XO (XO (XO (XO XH))))))) (Npos (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XO XH)))))))))))

mem_length0 :: Memory -> N
mem_length0 m =
  mem_length (mem_data m)

mem_size :: Memory -> N
mem_size m =
  div (mem_length0 m) page_size

load :: Memory -> N -> Static_offset -> Nat -> Option Bytes
load m n off l =
  case leb0 (add2 n (add2 off (of_nat l))) (mem_length0 m) of {
   True -> read_bytes m (add2 n off) l;
   False -> None}

sign_extend :: Sx -> Nat -> Bytes -> Bytes
sign_extend _ _ bs =
  bs

load_packed :: Sx -> Memory -> N -> Static_offset -> Nat -> Nat -> Option
               Bytes
load_packed s m n off lp l =
  option_map (sign_extend s l) (load m n off lp)

store :: Memory -> N -> Static_offset -> Bytes -> Nat -> Option Memory
store m n off bs l =
  case leb0 (add2 (add2 n off) (of_nat l)) (mem_length0 m) of {
   True -> write_bytes m (add2 n off) (bytes_takefill zero0 l bs);
   False -> None}

store_packed :: Memory -> N -> Static_offset -> Bytes -> Nat -> Option Memory
store_packed =
  store

wasm_deserialise :: Bytes -> Value_type -> Value
wasm_deserialise bs vt =
  case vt of {
   T_i32 -> VAL_int32 (unsafeCoerce repr2 (decode_int bs));
   T_i64 -> VAL_int64 (unsafeCoerce repr3 (decode_int bs));
   T_f32 -> VAL_float32 (unsafeCoerce of_bits0 (repr (decode_int bs)));
   T_f64 -> VAL_float64 (unsafeCoerce of_bits (repr1 (decode_int bs)))}

typeof :: Value -> Value_type
typeof v =
  case v of {
   VAL_int32 _ -> T_i32;
   VAL_int64 _ -> T_i64;
   VAL_float32 _ -> T_f32;
   VAL_float64 _ -> T_f64}

t_length :: Value_type -> Nat
t_length t =
  case t of {
   T_i32 -> S (S (S (S O)));
   T_f32 -> S (S (S (S O)));
   _ -> S (S (S (S (S (S (S (S O)))))))}

tp_length :: Packed_type -> Nat
tp_length tp =
  case tp of {
   Tp_i8 -> S O;
   Tp_i16 -> S (S O);
   Tp_i32 -> S (S (S (S O)))}

app_unop_i :: Type0 -> Unop_i -> Sort0 -> Sort0
app_unop_i e iop =
  case e of {
   Class _ intmx ->
    case iop of {
     UOI_clz -> int_clz intmx;
     UOI_ctz -> int_ctz intmx;
     UOI_popcnt -> int_popcnt intmx}}

app_unop_f :: Type1 -> Unop_f -> Sort1 -> Sort1
app_unop_f e fop =
  case e of {
   Class0 _ mx ->
    case fop of {
     UOF_neg -> float_neg mx;
     UOF_abs -> float_abs mx;
     UOF_ceil -> float_ceil mx;
     UOF_floor -> float_floor mx;
     UOF_trunc -> float_trunc mx;
     UOF_nearest -> float_nearest mx;
     UOF_sqrt -> float_sqrt mx}}

app_unop :: Unop -> Value -> Value
app_unop op0 v =
  case op0 of {
   Unop_i0 iop ->
    case v of {
     VAL_int32 c -> VAL_int32 (app_unop_i i32t iop c);
     VAL_int64 c -> VAL_int64 (app_unop_i i64t iop c);
     _ -> v};
   Unop_f0 fop ->
    case v of {
     VAL_float32 c -> VAL_float32 (app_unop_f f32t fop c);
     VAL_float64 c -> VAL_float64 (app_unop_f f64t fop c);
     _ -> v}}

app_binop_i :: Type0 -> Binop_i -> Sort0 -> Sort0 -> Option Sort0
app_binop_i e iop =
  case e of {
   Class _ mx ->
    case iop of {
     BOI_add -> let {f = int_add mx} in (\c1 c2 -> Some (f c1 c2));
     BOI_sub -> let {f = int_sub mx} in (\c1 c2 -> Some (f c1 c2));
     BOI_mul -> let {f = int_mul mx} in (\c1 c2 -> Some (f c1 c2));
     BOI_div s -> case s of {
                   SX_S -> int_div_s mx;
                   SX_U -> int_div_u mx};
     BOI_rem s -> case s of {
                   SX_S -> int_rem_s mx;
                   SX_U -> int_rem_u mx};
     BOI_and -> let {f = int_and mx} in (\c1 c2 -> Some (f c1 c2));
     BOI_or -> let {f = int_or mx} in (\c1 c2 -> Some (f c1 c2));
     BOI_xor -> let {f = int_xor mx} in (\c1 c2 -> Some (f c1 c2));
     BOI_shl -> let {f = int_shl mx} in (\c1 c2 -> Some (f c1 c2));
     BOI_shr s ->
      case s of {
       SX_S -> let {f = int_shr_s mx} in (\c1 c2 -> Some (f c1 c2));
       SX_U -> let {f = int_shr_u mx} in (\c1 c2 -> Some (f c1 c2))};
     BOI_rotl -> let {f = int_rotl mx} in (\c1 c2 -> Some (f c1 c2));
     BOI_rotr -> let {f = int_rotr mx} in (\c1 c2 -> Some (f c1 c2))}}

app_binop_f :: Type1 -> Binop_f -> Sort1 -> Sort1 -> Option Sort1
app_binop_f e fop =
  case e of {
   Class0 _ mx ->
    case fop of {
     BOF_add -> let {f = float_add mx} in (\c1 c2 -> Some (f c1 c2));
     BOF_sub -> let {f = float_sub mx} in (\c1 c2 -> Some (f c1 c2));
     BOF_mul -> let {f = float_mul mx} in (\c1 c2 -> Some (f c1 c2));
     BOF_div -> let {f = float_div mx} in (\c1 c2 -> Some (f c1 c2));
     BOF_min -> let {f = float_min mx} in (\c1 c2 -> Some (f c1 c2));
     BOF_max -> let {f = float_max mx} in (\c1 c2 -> Some (f c1 c2));
     BOF_copysign ->
      let {f = float_copysign mx} in (\c1 c2 -> Some (f c1 c2))}}

app_binop :: Binop -> Value -> Value -> Option Value
app_binop op0 v1 v2 =
  case op0 of {
   Binop_i0 iop ->
    case v1 of {
     VAL_int32 c1 ->
      case v2 of {
       VAL_int32 c2 ->
        option_map (\v -> VAL_int32 v) (app_binop_i i32t iop c1 c2);
       _ -> None};
     VAL_int64 c1 ->
      case v2 of {
       VAL_int64 c2 ->
        option_map (\v -> VAL_int64 v) (app_binop_i i64t iop c1 c2);
       _ -> None};
     _ -> None};
   Binop_f0 fop ->
    case v1 of {
     VAL_float32 c1 ->
      case v2 of {
       VAL_float32 c2 ->
        option_map (\v -> VAL_float32 v) (app_binop_f f32t fop c1 c2);
       _ -> None};
     VAL_float64 c1 ->
      case v2 of {
       VAL_float64 c2 ->
        option_map (\v -> VAL_float64 v) (app_binop_f f64t fop c1 c2);
       _ -> None};
     _ -> None}}

app_testop_i :: Type0 -> Sort0 -> Bool
app_testop_i e =
  case e of {
   Class _ mx -> int_eqz mx}

app_relop_i :: Type0 -> Relop_i -> Sort0 -> Sort0 -> Bool
app_relop_i e rop =
  case e of {
   Class base1 mx ->
    case rop of {
     ROI_eq -> int_eq mx;
     ROI_ne -> int_ne (Class base1 mx);
     ROI_lt s -> case s of {
                  SX_S -> int_lt_s mx;
                  SX_U -> int_lt_u mx};
     ROI_gt s -> case s of {
                  SX_S -> int_gt_s mx;
                  SX_U -> int_gt_u mx};
     ROI_le s -> case s of {
                  SX_S -> int_le_s mx;
                  SX_U -> int_le_u mx};
     ROI_ge s -> case s of {
                  SX_S -> int_ge_s mx;
                  SX_U -> int_ge_u mx}}}

app_relop_f :: Type1 -> Relop_f -> Sort1 -> Sort1 -> Bool
app_relop_f e rop =
  case e of {
   Class0 base1 mx ->
    case rop of {
     ROF_eq -> float_eq mx;
     ROF_ne -> float_ne (Class0 base1 mx);
     ROF_lt -> float_lt mx;
     ROF_gt -> float_gt mx;
     ROF_le -> float_le mx;
     ROF_ge -> float_ge mx}}

app_relop :: Relop -> Value -> Value -> Bool
app_relop op0 v1 v2 =
  case op0 of {
   Relop_i0 iop ->
    case v1 of {
     VAL_int32 c1 ->
      case v2 of {
       VAL_int32 c2 -> app_relop_i i32t iop c1 c2;
       _ -> False};
     VAL_int64 c1 ->
      case v2 of {
       VAL_int64 c2 -> app_relop_i i64t iop c1 c2;
       _ -> False};
     _ -> False};
   Relop_f0 fop ->
    case v1 of {
     VAL_float32 c1 ->
      case v2 of {
       VAL_float32 c2 -> app_relop_f f32t fop c1 c2;
       _ -> False};
     VAL_float64 c1 ->
      case v2 of {
       VAL_float64 c2 -> app_relop_f f64t fop c1 c2;
       _ -> False};
     _ -> False}}

cl_type :: Type -> (Function_closure Sort) -> Function_type
cl_type _ cl =
  case cl of {
   FC_func_native _ tf _ _ -> tf;
   FC_func_host tf _ -> tf}

option_bind :: (a1 -> Option a2) -> (Option a1) -> Option a2
option_bind f x =
  case x of {
   Some y -> f y;
   None -> None}

stypes :: Type -> (Store_record Sort) -> Instance -> Nat -> Option
          Function_type
stypes _ _ i j =
  nth_error (inst_types i) j

sglob_ind :: Type -> (Store_record Sort) -> Instance -> Nat -> Option Nat
sglob_ind _ _ i j =
  nth_error (inst_globs i) j

sglob :: Type -> (Store_record Sort) -> Instance -> Nat -> Option Global
sglob host_function1 s i j =
  option_bind (nth_error (s_globals s)) (sglob_ind host_function1 s i j)

sglob_val :: Type -> (Store_record Sort) -> Instance -> Nat -> Option Value
sglob_val host_function1 s i j =
  option_map g_val (sglob host_function1 s i j)

stab_index :: Type -> (Store_record Sort) -> Nat -> Nat -> Option Nat
stab_index _ s i j =
  option_bind (\x -> x)
    (option_bind (\stab_i -> nth_error (table_data stab_i) j)
      (nth_error (s_tables s) i))

stab_addr :: Type -> (Store_record Sort) -> Frame -> Nat -> Option Nat
stab_addr host_function1 s f c =
  case inst_tab (f_inst f) of {
   Nil -> None;
   Cons ta _ -> stab_index host_function1 s ta c}

update_list_at :: (List a1) -> Nat -> a1 -> List a1
update_list_at l k a =
  cat (take k l) (cat (Cons a Nil) (skipn (addn k (S O)) l))

supdate_glob_s :: Type -> (Store_record Sort) -> Nat -> Value -> Option
                  (Store_record Sort)
supdate_glob_s _ s k v =
  option_map (\g -> Build_store_record (s_funcs s) (s_tables s) (s_mems s)
    (update_list_at (s_globals s) k (Build_global (g_mut g) v)))
    (nth_error (s_globals s) k)

supdate_glob :: Type -> (Store_record Sort) -> Instance -> Nat -> Value ->
                Option (Store_record Sort)
supdate_glob host_function1 s i j v =
  option_bind (\k -> supdate_glob_s host_function1 s k v)
    (sglob_ind host_function1 s i j)

is_const :: Administrative_instruction -> Bool
is_const e =
  case e of {
   AI_basic b -> case b of {
                  BI_const _ -> True;
                  _ -> False};
   _ -> False}

const_list :: (List Administrative_instruction) -> Bool
const_list es =
  forallb is_const es

to_e_list :: (List Basic_instruction) -> List Administrative_instruction
to_e_list bes =
  map0 (\x -> AI_basic x) bes

to_b_single :: Administrative_instruction -> Basic_instruction
to_b_single e =
  case e of {
   AI_basic x -> x;
   _ -> BI_const (VAL_int32 (unsafeCoerce zero1))}

to_b_list :: (List Administrative_instruction) -> List Basic_instruction
to_b_list es =
  map0 to_b_single es

type Es_is_basic = Any

v_to_e_list :: (List Value) -> List Administrative_instruction
v_to_e_list ves =
  map0 (\v -> AI_basic (BI_const v)) ves

result_to_stack :: Result -> List Administrative_instruction
result_to_stack r =
  case r of {
   Result_values vs -> v_to_e_list vs;
   Result_trap -> Cons AI_trap Nil}

lfill :: Nat -> Lholed -> (List Administrative_instruction) -> Option
         (List Administrative_instruction)
lfill k lh es =
  case k of {
   O ->
    case lh of {
     LH_base vs es' ->
      case const_list vs of {
       True -> Some (app vs (app es es'));
       False -> None};
     LH_rec _ _ _ _ _ -> None};
   S k' ->
    case lh of {
     LH_base _ _ -> None;
     LH_rec vs n es' lh' es'' ->
      case const_list vs of {
       True ->
        case lfill k' lh' es of {
         Some lfilledk -> Some (app vs (Cons (AI_label n es' lfilledk) es''));
         None -> None};
       False -> None}}}

data LfilledInd =
   LfilledBase (List Administrative_instruction) (List
                                                 Administrative_instruction) 
 (List Administrative_instruction)
 | LfilledRec Nat (List Administrative_instruction) Nat (List
                                                        Administrative_instruction) 
 Lholed (List Administrative_instruction) (List Administrative_instruction) 
 (List Administrative_instruction) LfilledInd

lfilledInd_rect :: ((List Administrative_instruction) -> (List
                   Administrative_instruction) -> (List
                   Administrative_instruction) -> () -> a1) -> (Nat -> (List
                   Administrative_instruction) -> Nat -> (List
                   Administrative_instruction) -> Lholed -> (List
                   Administrative_instruction) -> (List
                   Administrative_instruction) -> (List
                   Administrative_instruction) -> () -> LfilledInd -> a1 ->
                   a1) -> Nat -> Lholed -> (List Administrative_instruction)
                   -> (List Administrative_instruction) -> LfilledInd -> a1
lfilledInd_rect f f0 _ _ _ _ l =
  case l of {
   LfilledBase vs es es' -> f vs es es' __;
   LfilledRec k vs n es' lh' es'' es lI l0 ->
    f0 k vs n es' lh' es'' es lI __ l0 (lfilledInd_rect f f0 k lh' es lI l0)}

lfilled_Ind_Equivalent :: Nat -> Lholed -> (List Administrative_instruction)
                          -> (List Administrative_instruction) -> Prod
                          (() -> LfilledInd) ()
lfilled_Ind_Equivalent k lh es lI =
  Pair
    (nat_rect (\lh0 es0 lI0 _ ->
      case lh0 of {
       LH_base l l0 ->
        let {b = const_list l} in
        case b of {
         True -> eq_rect (cat l (cat es0 l0)) (LfilledBase l es0 l0) lI0;
         False -> false_rect};
       LH_rec _ _ _ _ _ -> false_rect}) (\k0 iHk lh0 es0 lI0 _ ->
      case lh0 of {
       LH_base _ _ -> false_rect;
       LH_rec l n l0 lh1 l1 ->
        let {b = const_list l} in
        case b of {
         True ->
          let {o = lfill k0 lh1 es0} in
          case o of {
           Some l2 ->
            eq_rect (cat l (cat (Cons (AI_label n l0 l2) Nil) l1))
              (LfilledRec k0 l n l0 lh1 l1 es0 l2 (iHk lh1 es0 l2 __)) lI0;
           None -> false_rect};
         False -> false_rect}}) k lh es lI) __

cvt_i32 :: (Option Sx) -> Value -> Option Sort
cvt_i32 s v =
  case v of {
   VAL_int32 _ -> None;
   VAL_int64 c -> Some (wasm_wrap c);
   VAL_float32 c ->
    case s of {
     Some _ -> float_ui32_trunc f32m c;
     None -> None};
   VAL_float64 c ->
    case s of {
     Some _ -> float_ui32_trunc f64m c;
     None -> None}}

cvt_i64 :: (Option Sx) -> Value -> Option Sort
cvt_i64 s v =
  case v of {
   VAL_int32 c ->
    case s of {
     Some s0 ->
      case s0 of {
       SX_S -> Some (wasm_extend_s c);
       SX_U -> Some (wasm_extend_u c)};
     None -> None};
   VAL_int64 _ -> None;
   VAL_float32 c ->
    case s of {
     Some s0 ->
      case s0 of {
       SX_S -> float_si64_trunc f32m c;
       SX_U -> float_ui64_trunc f32m c};
     None -> None};
   VAL_float64 c ->
    case s of {
     Some s0 ->
      case s0 of {
       SX_S -> float_si64_trunc f64m c;
       SX_U -> float_ui64_trunc f64m c};
     None -> None}}

cvt_f32 :: (Option Sx) -> Value -> Option Sort
cvt_f32 s v =
  case v of {
   VAL_int32 c ->
    case s of {
     Some s0 ->
      case s0 of {
       SX_S -> Some (float_convert_si32 f32m c);
       SX_U -> Some (float_convert_ui32 f32m c)};
     None -> None};
   VAL_int64 c ->
    case s of {
     Some s0 ->
      case s0 of {
       SX_S -> Some (float_convert_si64 f32m c);
       SX_U -> Some (float_convert_ui64 f32m c)};
     None -> None};
   VAL_float32 _ -> None;
   VAL_float64 c -> Some (wasm_demote c)}

cvt_f64 :: (Option Sx) -> Value -> Option Sort
cvt_f64 s v =
  case v of {
   VAL_int32 c ->
    case s of {
     Some s0 ->
      case s0 of {
       SX_S -> Some (float_convert_si32 f64m c);
       SX_U -> Some (float_convert_ui32 f64m c)};
     None -> None};
   VAL_int64 c ->
    case s of {
     Some s0 ->
      case s0 of {
       SX_S -> Some (float_convert_si64 f64m c);
       SX_U -> Some (float_convert_ui64 f64m c)};
     None -> None};
   VAL_float32 c -> Some (wasm_promote c);
   VAL_float64 _ -> None}

cvt :: Value_type -> (Option Sx) -> Value -> Option Value
cvt t s v =
  case t of {
   T_i32 -> option_map (\x -> VAL_int32 x) (cvt_i32 s v);
   T_i64 -> option_map (\x -> VAL_int64 x) (cvt_i64 s v);
   T_f32 -> option_map (\x -> VAL_float32 x) (cvt_f32 s v);
   T_f64 -> option_map (\x -> VAL_float64 x) (cvt_f64 s v)}

bits :: Value -> Bytes
bits v =
  case v of {
   VAL_int32 c -> serialise_i32 c;
   VAL_int64 c -> serialise_i64 c;
   VAL_float32 c -> serialise_f32 c;
   VAL_float64 c -> serialise_f64 c}

bitzero :: Value_type -> Value
bitzero t =
  case t of {
   T_i32 -> VAL_int32 (int_zero i32m);
   T_i64 -> VAL_int64 (int_zero i64m);
   T_f32 -> VAL_float32 (float_zero f32m);
   T_f64 -> VAL_float64 (float_zero f64m)}

n_zeros :: (List Value_type) -> List Value
n_zeros ts =
  map0 bitzero ts

upd_label :: T_context -> (List (List Value_type)) -> T_context
upd_label c lab =
  Build_t_context (tc_types_t c) (tc_func_t c) (tc_global c) (tc_table c)
    (tc_memory c) (tc_local c) lab (tc_return c)

data Be_typing =
   Bet_const T_context Value
 | Bet_unop T_context Value_type Unop
 | Bet_binop T_context Value_type Binop
 | Bet_testop T_context Value_type
 | Bet_relop T_context Value_type Relop
 | Bet_convert T_context Value_type Value_type (Option Sx)
 | Bet_reinterpret T_context Value_type Value_type
 | Bet_unreachable T_context Result_type Result_type
 | Bet_nop T_context
 | Bet_drop T_context Value_type
 | Bet_select T_context Value_type
 | Bet_block T_context Result_type Result_type (List Basic_instruction) 
 Be_typing
 | Bet_loop T_context (List Value_type) Result_type (List Basic_instruction) 
 Be_typing
 | Bet_if_wasm T_context Result_type (List Value_type) (List
                                                       Basic_instruction) 
 (List Basic_instruction) Be_typing Be_typing
 | Bet_br T_context Nat (List Sort) Sort Result_type
 | Bet_br_if T_context Nat Sort
 | Bet_br_table T_context Nat (List Nat) Sort (List Sort) Result_type
 | Bet_return T_context (List Value_type) (List Value_type) Result_type
 | Bet_call T_context Nat Function_type
 | Bet_call_indirect T_context Nat Result_type Result_type
 | Bet_get_local T_context Nat Value_type
 | Bet_set_local T_context Nat Value_type
 | Bet_tee_local T_context Nat Value_type
 | Bet_get_global T_context Nat Value_type
 | Bet_set_global T_context Nat Global_type Value_type
 | Bet_load T_context Alignment_exponent Static_offset (Option
                                                       (Prod Packed_type Sx)) 
 Value_type
 | Bet_store T_context Alignment_exponent Static_offset (Option Packed_type) 
 Value_type
 | Bet_current_memory T_context
 | Bet_grow_memory T_context
 | Bet_empty T_context
 | Bet_composition T_context (List Basic_instruction) Basic_instruction 
 Result_type Result_type Result_type Be_typing Be_typing
 | Bet_weakening T_context (List Basic_instruction) (List Value_type) 
 Result_type Result_type Be_typing

be_typing_rect :: (T_context -> Value -> a1) -> (T_context -> Value_type ->
                  Unop -> () -> a1) -> (T_context -> Value_type -> Binop ->
                  () -> a1) -> (T_context -> Value_type -> () -> () -> a1) ->
                  (T_context -> Value_type -> Relop -> () -> a1) ->
                  (T_context -> Value_type -> Value_type -> (Option Sx) -> ()
                  -> () -> a1) -> (T_context -> Value_type -> Value_type ->
                  () -> () -> a1) -> (T_context -> Result_type -> Result_type
                  -> a1) -> (T_context -> a1) -> (T_context -> Value_type ->
                  a1) -> (T_context -> Value_type -> a1) -> (T_context ->
                  Result_type -> Result_type -> (List Basic_instruction) ->
                  Be_typing -> a1 -> a1) -> (T_context -> (List Value_type)
                  -> Result_type -> (List Basic_instruction) -> Be_typing ->
                  a1 -> a1) -> (T_context -> Result_type -> (List Value_type)
                  -> (List Basic_instruction) -> (List Basic_instruction) ->
                  Be_typing -> a1 -> Be_typing -> a1 -> a1) -> (T_context ->
                  Nat -> (List Sort) -> Sort -> Result_type -> () -> () ->
                  a1) -> (T_context -> Nat -> Sort -> () -> () -> a1) ->
                  (T_context -> Nat -> (List Nat) -> Sort -> (List Sort) ->
                  Result_type -> () -> a1) -> (T_context -> (List Value_type)
                  -> (List Value_type) -> Result_type -> () -> a1) ->
                  (T_context -> Nat -> Function_type -> () -> () -> a1) ->
                  (T_context -> Nat -> Result_type -> Result_type -> () -> ()
                  -> () -> a1) -> (T_context -> Nat -> Value_type -> () -> ()
                  -> a1) -> (T_context -> Nat -> Value_type -> () -> () ->
                  a1) -> (T_context -> Nat -> Value_type -> () -> () -> a1)
                  -> (T_context -> Nat -> Value_type -> () -> () -> a1) ->
                  (T_context -> Nat -> Global_type -> Value_type -> () -> ()
                  -> () -> () -> a1) -> (T_context -> Alignment_exponent ->
                  Static_offset -> (Option (Prod Packed_type Sx)) ->
                  Value_type -> () -> () -> a1) -> (T_context ->
                  Alignment_exponent -> Static_offset -> (Option Packed_type)
                  -> Value_type -> () -> () -> a1) -> (T_context -> () -> a1)
                  -> (T_context -> () -> a1) -> (T_context -> a1) ->
                  (T_context -> (List Basic_instruction) -> Basic_instruction
                  -> Result_type -> Result_type -> Result_type -> Be_typing
                  -> a1 -> Be_typing -> a1 -> a1) -> (T_context -> (List
                  Basic_instruction) -> (List Value_type) -> Result_type ->
                  Result_type -> Be_typing -> a1 -> a1) -> T_context -> (List
                  Basic_instruction) -> Function_type -> Be_typing -> a1
be_typing_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 _ _ _ b =
  case b of {
   Bet_const c v -> f c v;
   Bet_unop c t op0 -> f0 c t op0 __;
   Bet_binop c t op0 -> f1 c t op0 __;
   Bet_testop c t -> f2 c t __ __;
   Bet_relop c t op0 -> f3 c t op0 __;
   Bet_convert c t1 t2 sx -> f4 c t1 t2 sx __ __;
   Bet_reinterpret c t1 t2 -> f5 c t1 t2 __ __;
   Bet_unreachable c ts ts' -> f6 c ts ts';
   Bet_nop c -> f7 c;
   Bet_drop c t -> f8 c t;
   Bet_select c t -> f9 c t;
   Bet_block c tn tm es x ->
    f10 c tn tm es x
      (be_typing_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30
        (upd_label c (app (Cons tm Nil) (tc_label c))) es (Tf tn tm) x);
   Bet_loop c tn tm es b0 ->
    f11 c tn tm es b0
      (be_typing_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30
        (upd_label c (app (Cons tn Nil) (tc_label c))) es (Tf tn tm) b0);
   Bet_if_wasm c tn tm es1 es2 b0 b1 ->
    f12 c tn tm es1 es2 b0
      (be_typing_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30
        (upd_label c (app (Cons tm Nil) (tc_label c))) es1 (Tf tn tm) b0) b1
      (be_typing_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30
        (upd_label c (app (Cons tm Nil) (tc_label c))) es2 (Tf tn tm) b1);
   Bet_br c i t1s ts t2s -> f13 c i t1s ts t2s __ __;
   Bet_br_if c i ts -> f14 c i ts __ __;
   Bet_br_table c i ins ts t1s t2s -> f15 c i ins ts t1s t2s __;
   Bet_return c ts t1s t2s -> f16 c ts t1s t2s __;
   Bet_call c i tf -> f17 c i tf __ __;
   Bet_call_indirect c i t1s t2s -> f18 c i t1s t2s __ __ __;
   Bet_get_local c i t -> f19 c i t __ __;
   Bet_set_local c i t -> f20 c i t __ __;
   Bet_tee_local c i t -> f21 c i t __ __;
   Bet_get_global c i t -> f22 c i t __ __;
   Bet_set_global c i g t -> f23 c i g t __ __ __ __;
   Bet_load c a off tp_sx t -> f24 c a off tp_sx t __ __;
   Bet_store c a off tp t -> f25 c a off tp t __ __;
   Bet_current_memory c -> f26 c __;
   Bet_grow_memory c -> f27 c __;
   Bet_empty c -> f28 c;
   Bet_composition c es e t1s t2s t3s b0 b1 ->
    f29 c es e t1s t2s t3s b0
      (be_typing_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 c es (Tf
        t1s t2s) b0) b1
      (be_typing_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 c (Cons e
        Nil) (Tf t2s t3s) b1);
   Bet_weakening c es ts t1s t2s b0 ->
    f30 c es ts t1s t2s b0
      (be_typing_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 c es (Tf
        t1s t2s) b0)}

upd_local :: T_context -> (List Value_type) -> T_context
upd_local c loc =
  Build_t_context (tc_types_t c) (tc_func_t c) (tc_global c) (tc_table c)
    (tc_memory c) loc (tc_label c) (tc_return c)

upd_return :: T_context -> (Option (List Value_type)) -> T_context
upd_return c ret0 =
  Build_t_context (tc_types_t c) (tc_func_t c) (tc_global c) (tc_table c)
    (tc_memory c) (tc_local c) (tc_label c) ret0

upd_local_return :: T_context -> (List Value_type) -> (Option
                    (List Value_type)) -> T_context
upd_local_return c loc ret0 =
  Build_t_context (tc_types_t c) (tc_func_t c) (tc_global c) (tc_table c)
    (tc_memory c) loc (tc_label c) ret0

upd_local_label_return :: T_context -> (List Value_type) -> (List
                          (List Value_type)) -> (Option (List Value_type)) ->
                          T_context
upd_local_label_return c loc lab ret0 =
  Build_t_context (tc_types_t c) (tc_func_t c) (tc_global c) (tc_table c)
    (tc_memory c) loc lab ret0

data Frame_typing =
   Mk_frame_typing (Store_record Sort) Instance (List Value_type) T_context 
 Frame

data Cl_typing =
   Cl_typing_native Instance (Store_record Sort) T_context T_context 
 (List Value_type) Result_type Result_type (List Basic_instruction) Function_type 
 Be_typing
 | Cl_typing_host (Store_record Sort) Function_type Sort

data E_typing =
   Ety_a (Store_record Sort) T_context (List Basic_instruction) Function_type 
 Be_typing
 | Ety_composition (Store_record Sort) T_context (List
                                                 Administrative_instruction) 
 Administrative_instruction Result_type Result_type Result_type E_typing 
 E_typing
 | Ety_weakening (Store_record Sort) T_context (List
                                               Administrative_instruction) 
 (List Value_type) Result_type Result_type E_typing
 | Ety_trap (Store_record Sort) T_context Function_type
 | Ety_local (Store_record Sort) T_context Nat Frame (List
                                                     Administrative_instruction) 
 (List Value_type) S_typing
 | Ety_invoke (Store_record Sort) Nat T_context (Function_closure Sort) 
 Function_type Cl_typing
 | Ety_label (Store_record Sort) T_context (List Administrative_instruction) 
 (List Administrative_instruction) Result_type Result_type Nat E_typing 
 E_typing
data S_typing =
   Mk_s_typing (Store_record Sort) Frame (List Administrative_instruction) 
 (Option (List Value_type)) Result_type T_context T_context Frame_typing 
 E_typing

e_typing_rect :: Type -> ((Store_record Sort) -> T_context -> (List
                 Basic_instruction) -> Function_type -> Be_typing -> a1) ->
                 ((Store_record Sort) -> T_context -> (List
                 Administrative_instruction) -> Administrative_instruction ->
                 Result_type -> Result_type -> Result_type -> E_typing -> a1
                 -> E_typing -> a1 -> a1) -> ((Store_record Sort) ->
                 T_context -> (List Administrative_instruction) -> (List
                 Value_type) -> Result_type -> Result_type -> E_typing -> a1
                 -> a1) -> ((Store_record Sort) -> T_context -> Function_type
                 -> a1) -> ((Store_record Sort) -> T_context -> Nat -> Frame
                 -> (List Administrative_instruction) -> (List Value_type) ->
                 S_typing -> () -> a1) -> ((Store_record Sort) -> Nat ->
                 T_context -> (Function_closure Sort) -> Function_type -> ()
                 -> Cl_typing -> a1) -> ((Store_record Sort) -> T_context ->
                 (List Administrative_instruction) -> (List
                 Administrative_instruction) -> Result_type -> Result_type ->
                 Nat -> E_typing -> a1 -> E_typing -> a1 -> () -> a1) ->
                 (Store_record Sort) -> T_context -> (List
                 Administrative_instruction) -> Function_type -> E_typing ->
                 a1
e_typing_rect host_function1 f f0 f1 f2 f3 f4 f5 _ _ _ _ e =
  case e of {
   Ety_a s c bes tf b -> f s c bes tf b;
   Ety_composition s c es e0 t1s t2s t3s e1 e2 ->
    f0 s c es e0 t1s t2s t3s e1
      (e_typing_rect host_function1 f f0 f1 f2 f3 f4 f5 s c es (Tf t1s t2s)
        e1) e2
      (e_typing_rect host_function1 f f0 f1 f2 f3 f4 f5 s c (Cons e0 Nil) (Tf
        t2s t3s) e2);
   Ety_weakening s c es ts t1s t2s e0 ->
    f1 s c es ts t1s t2s e0
      (e_typing_rect host_function1 f f0 f1 f2 f3 f4 f5 s c es (Tf t1s t2s)
        e0);
   Ety_trap s c tf -> f2 s c tf;
   Ety_local s c n f6 es ts s0 -> f3 s c n f6 es ts s0 __;
   Ety_invoke s a c cl tf c0 -> f4 s a c cl tf __ c0;
   Ety_label s c e0s es ts t2s n e0 e1 ->
    f5 s c e0s es ts t2s n e0
      (e_typing_rect host_function1 f f0 f1 f2 f3 f4 f5 s c e0s (Tf ts t2s)
        e0) e1
      (e_typing_rect host_function1 f f0 f1 f2 f3 f4 f5 s
        (upd_label c (cat (Cons ts Nil) (tc_label c))) es (Tf Nil t2s) e1) __}

e_typing_ind' :: Type -> ((Store_record Sort) -> T_context -> (List
                 Basic_instruction) -> Function_type -> Be_typing -> a1) ->
                 ((Store_record Sort) -> T_context -> (List
                 Administrative_instruction) -> Administrative_instruction ->
                 Result_type -> Result_type -> Result_type -> E_typing -> a1
                 -> E_typing -> a1 -> a1) -> ((Store_record Sort) ->
                 T_context -> (List Administrative_instruction) -> (List
                 Value_type) -> Result_type -> Result_type -> E_typing -> a1
                 -> a1) -> ((Store_record Sort) -> T_context -> Function_type
                 -> a1) -> ((Store_record Sort) -> T_context -> Nat -> Frame
                 -> (List Administrative_instruction) -> (List Value_type) ->
                 S_typing -> a2 -> () -> a1) -> ((Store_record Sort) -> Nat
                 -> T_context -> (Function_closure Sort) -> Function_type ->
                 () -> Cl_typing -> a1) -> ((Store_record Sort) -> T_context
                 -> (List Administrative_instruction) -> (List
                 Administrative_instruction) -> Result_type -> Result_type ->
                 Nat -> E_typing -> a1 -> E_typing -> a1 -> () -> a1) ->
                 ((Store_record Sort) -> Frame -> (List
                 Administrative_instruction) -> (Option (List Value_type)) ->
                 Result_type -> T_context -> T_context -> Frame_typing -> ()
                 -> E_typing -> a1 -> () -> a2) -> (Store_record Sort) ->
                 T_context -> (List Administrative_instruction) ->
                 Function_type -> E_typing -> a1
e_typing_ind' _ f f0 f1 f2 f3 f4 f5 f6 s t l f7 e =
  let {
   f8 _ _ _ _ e0 =
     case e0 of {
      Ety_a s0 c bes tf b -> f s0 c bes tf b;
      Ety_composition s0 c es e1 t1s t2s t3s e2 e3 ->
       f0 s0 c es e1 t1s t2s t3s e2 (f8 s0 c es (Tf t1s t2s) e2) e3
         (f8 s0 c (Cons e1 Nil) (Tf t2s t3s) e3);
      Ety_weakening s0 c es ts t1s t2s e1 ->
       f1 s0 c es ts t1s t2s e1 (f8 s0 c es (Tf t1s t2s) e1);
      Ety_trap s0 c tf -> f2 s0 c tf;
      Ety_local s0 c n f10 es ts s1 ->
       f3 s0 c n f10 es ts s1 (f9 s0 (Some ts) f10 es ts s1) __;
      Ety_invoke s0 a c cl tf c0 -> f4 s0 a c cl tf __ c0;
      Ety_label s0 c e0s es ts t2s n e1 e2 ->
       f5 s0 c e0s es ts t2s n e1 (f8 s0 c e0s (Tf ts t2s) e1) e2
         (f8 s0 (upd_label c (cat (Cons ts Nil) (tc_label c))) es (Tf Nil
           t2s) e2) __};
   f9 _ _ _ _ _ s0 =
     case s0 of {
      Mk_s_typing s1 f10 es rs ts c c0 f11 e0 ->
       f6 s1 f10 es rs ts c c0 f11 __ e0 (f8 s1 c es (Tf Nil ts) e0) __}}
  in f8 s t l f7 e

type Store_typing = Any

data Config_typing =
   Mk_config_typing (Store_record Sort) Frame (List
                                              Administrative_instruction) 
 (List Value_type) Store_typing S_typing

type Ident a = a
  -- singleton inductive, whose constructor was mkIdent
  
unIdent :: (Ident a1) -> a1
unIdent i =
  i

monad_ident :: Monad (Ident Any)
monad_ident =
  Build_Monad (\_ v -> v) (\_ _ c f -> f (unIdent c))

data Host =
   Build_host Type (Sort -> Function_type -> (Store_record Sort) -> Sort ->
                   (List Value) -> Sort -> (Store_record Sort) -> Result ->
                   () -> Store_typing -> Store_typing)

host_state :: Type -> Host -> Type
host_state _ h =
  case h of {
   Build_host host_state1 _ -> host_state1}

data Executable_host host_function =
   Make_executable_host (Monad Any) ((Store_record host_function) ->
                                    Function_type -> host_function -> (List
                                    Value) -> Any)

type Host_function = Empty_set

type Host_event a = Ident a

host_ret :: a1 -> Ident a1
host_ret x =
  ret (unsafeCoerce monad_ident) x

host_bind :: (Ident a1) -> (a1 -> Ident a2) -> Ident a2
host_bind x x0 =
  bind0 (unsafeCoerce monad_ident) (unsafeCoerce x) x0

type Store_record0 = Store_record Host_function

host_apply :: Store_record0 -> Function_type -> Empty_set -> (List Value) ->
              Ident (Option (Prod Store_record0 Result))
host_apply _ _ =
  of_void

host_function_eq_dec :: Host_function -> Host_function -> Sumbool
host_function_eq_dec =
  unsafeCoerce eq_comparable void_eqType

host_function_eqb :: Host_function -> Host_function -> Bool
host_function_eqb f1 f2 =
  is_left (host_function_eq_dec f1 f2)

host_functionP :: Axiom Host_function
host_functionP =
  eq_dec_Equality_axiom host_function_eq_dec

host_function_eqMixin :: Mixin_of Host_function
host_function_eqMixin =
  Mixin host_function_eqb host_functionP

host_function :: Type
host_function =
  unsafeCoerce host_function_eqMixin

type Executable_host0 = Executable_host Host_function

type Store_record1 = Store_record Host_function

type Config_tuple0 = Config_tuple Host_function

type Function_closure0 = Function_closure Host_function

type Res_tuple0 = Res_tuple Host_function

host_monad :: Monad (Host_event Any)
host_monad =
  Build_Monad (\_ -> host_ret) (\_ _ -> host_bind)

executable_host_instance :: Executable_host0
executable_host_instance =
  Make_executable_host (unsafeCoerce host_monad) (unsafeCoerce host_apply)

host_functor :: Functor (Host_event Any)
host_functor =
  functor_Monad host_monad

type Host0 = Host

host_instance :: Host0
host_instance =
  Build_host unit_eqType (\_ _ _ _ _ _ _ _ _ _ -> false_rect)

data Reduce_simple =
   Rs_unop Value Unop Value_type
 | Rs_binop_success Value Value Value Binop Value_type
 | Rs_binop_failure Value Value Binop Value_type
 | Rs_testop_i32 Sort
 | Rs_testop_i64 Sort
 | Rs_relop Value Value Value_type Relop
 | Rs_convert_success Value_type Value_type Value Value (Option Sx)
 | Rs_convert_failure Value_type Value_type Value (Option Sx)
 | Rs_reinterpret Value_type Value_type Value
 | Rs_unreachable
 | Rs_nop
 | Rs_drop Value
 | Rs_select_false Sort Value Value
 | Rs_select_true Sort Value Value
 | Rs_block (List Administrative_instruction) (List Basic_instruction) 
 Nat Nat (List Value_type) (List Value_type)
 | Rs_loop (List Administrative_instruction) (List Basic_instruction) 
 Nat Nat (List Value_type) (List Value_type)
 | Rs_if_false Sort Function_type (List Basic_instruction) (List
                                                           Basic_instruction)
 | Rs_if_true Sort Function_type (List Basic_instruction) (List
                                                          Basic_instruction)
 | Rs_label_const Nat (List Administrative_instruction) (List
                                                        Administrative_instruction)
 | Rs_label_trap Nat (List Administrative_instruction)
 | Rs_br Nat (List Administrative_instruction) (List
                                               Administrative_instruction) 
 Nat (List Administrative_instruction) Lholed
 | Rs_br_if_false Sort Immediate
 | Rs_br_if_true Sort Immediate
 | Rs_br_table (List Immediate) Sort Immediate Immediate
 | Rs_br_table_length (List Immediate) Sort Immediate
 | Rs_local_const (List Administrative_instruction) Nat Frame
 | Rs_local_trap Nat Frame
 | Rs_return Nat Nat (List Administrative_instruction) (List
                                                       Administrative_instruction) 
 Lholed Frame
 | Rs_tee_local Immediate Administrative_instruction
 | Rs_trap (List Administrative_instruction) Lholed

data Reduce =
   R_simple (List Administrative_instruction) (List
                                              Administrative_instruction) 
 (Store_record Sort) Frame Sort Reduce_simple
 | R_call (Store_record Sort) Frame Nat Funcaddr Sort
 | R_call_indirect_success (Store_record Sort) Frame Nat Nat (Function_closure
                                                             Sort) Sort 
 Sort
 | R_call_indirect_failure1 (Store_record Sort) Frame Nat Nat (Function_closure
                                                              Sort) Sort 
 Sort
 | R_call_indirect_failure2 (Store_record Sort) Frame Immediate Sort 
 Sort
 | R_invoke_native Nat (Function_closure Sort) Result_type Result_type 
 (List Value_type) (List Basic_instruction) (List Administrative_instruction) 
 (List Value) Nat Nat Nat (List Value) (Store_record Sort) Frame Frame 
 Instance Sort
 | R_invoke_host_success Nat (Function_closure Sort) Sort Result_type 
 Result_type (List Administrative_instruction) (List Value) Nat Nat (Store_record
                                                                    Sort) 
 (Store_record Sort) Result Frame Sort Sort
 | R_invoke_host_diverge Nat (Function_closure Sort) Result_type Result_type 
 Sort (List Administrative_instruction) (List Value) Nat Nat (Store_record
                                                             Sort) Frame 
 Sort Sort
 | R_get_local Frame Value Nat (Store_record Sort) Sort
 | R_set_local Frame Frame Nat Value (Store_record Sort) Value Sort
 | R_get_global (Store_record Sort) Frame Nat Value Sort
 | R_set_global (Store_record Sort) Frame Nat Value (Store_record Sort) 
 Sort
 | R_load_success (Store_record Sort) Nat Frame Value_type Bytes Sort 
 Alignment_exponent Static_offset Memory Sort
 | R_load_failure (Store_record Sort) Nat Frame Value_type Sort Alignment_exponent 
 Static_offset Memory Sort
 | R_load_packed_success (Store_record Sort) Nat Frame Value_type Packed_type 
 Sort Alignment_exponent Static_offset Memory Bytes Sx Sort
 | R_load_packed_failure (Store_record Sort) Nat Frame Value_type Packed_type 
 Sort Alignment_exponent Static_offset Memory Sx Sort
 | R_store_success Value_type Value (Store_record Sort) Nat Frame Memory 
 Sort Alignment_exponent Static_offset Memory Sort
 | R_store_failure Value_type Value (Store_record Sort) Nat Frame Memory 
 Sort Static_offset Alignment_exponent Sort
 | R_store_packed_success Value_type Value (Store_record Sort) Nat Frame 
 Memory Sort Static_offset Alignment_exponent Memory Packed_type Sort
 | R_store_packed_failure Value_type Value (Store_record Sort) Nat Frame 
 Memory Sort Static_offset Alignment_exponent Packed_type Sort
 | R_current_memory Nat Frame Memory N (Store_record Sort) Sort
 | R_grow_memory_success (Store_record Sort) Nat Frame Memory N Memory 
 Sort Sort
 | R_grow_memory_failure Nat Frame Memory N (Store_record Sort) Sort 
 Sort
 | R_label (Store_record Sort) Frame (List Administrative_instruction) 
 (List Administrative_instruction) (Store_record Sort) Frame (List
                                                             Administrative_instruction) 
 (List Administrative_instruction) Nat Lholed Sort Sort Reduce
 | R_local (Store_record Sort) Frame (List Administrative_instruction) 
 (Store_record Sort) Frame (List Administrative_instruction) Nat Frame 
 Sort Sort Reduce

p0 :: (Nat -> (Nat -> () -> a1) -> a1) -> a1
p0 iH =
  iH O (\_ _ -> false_rect)

strong_rect_all :: (Nat -> (Nat -> () -> a1) -> a1) -> Nat -> Nat -> a1
strong_rect_all iH n m =
  nat_rect (\m0 _ -> eq_rect_r O (\_ -> p0 iH) m0 __) (\_ iHn m0 _ ->
    iH m0 (\m' _ -> iHn m' __)) n m __

strong_rect :: (Nat -> (Nat -> () -> a1) -> a1) -> Nat -> a1
strong_rect iH n =
  iH n (\n0 _ -> iH n0 (\n1 _ -> iH n1 (\n2 _ -> strong_rect_all iH n2 n2)))

to_e_list_basic :: (List Basic_instruction) -> Es_is_basic
to_e_list_basic bes =
  list_rect __ (\a _ iHbes -> unsafeCoerce (Pair (ExistT a __) iHbes)) bes

basic_concat :: (List Administrative_instruction) -> (List
                Administrative_instruction) -> Es_is_basic -> Prod
                Es_is_basic Es_is_basic
basic_concat es1 =
  list_rect (\_ x -> Pair __ x) (\_ _ iHes1 es2 h ->
    case unsafeCoerce h of {
     Pair h0 h1 ->
      let {h2 = iHes1 es2 h1} in
      case h2 of {
       Pair e e0 -> Pair (unsafeCoerce (Pair h0 e)) e0}}) es1

const_list_is_basic :: (List Administrative_instruction) -> Es_is_basic
const_list_is_basic es =
  list_rect __ (\a _ iHes _ ->
    unsafeCoerce (Pair
      (case a of {
        AI_basic b -> ExistT b __;
        _ -> false_rect}) (iHes __))) es __

const_es_exists :: (List Administrative_instruction) -> SigT (List Value) ()
const_es_exists es =
  list_rect (\_ -> ExistT Nil __) (\a _ iHes _ ->
    case a of {
     AI_basic b ->
      case b of {
       BI_const v ->
        let {s = iHes __} in
        case s of {
         ExistT vs _ -> ExistT (Cons v vs) __};
       _ -> false_rect};
     _ -> false_rect}) es __

b_e_elim :: (List Basic_instruction) -> (List Administrative_instruction) ->
            Prod () Es_is_basic
b_e_elim bes es =
  list_rect (\es0 _ ->
    let {_evar_0_ = Pair __ __} in
    eq_rect (to_e_list Nil) (unsafeCoerce _evar_0_) es0) (\a bes0 _ es0 _ ->
    let {_evar_0_ = Pair __ (to_e_list_basic (Cons a bes0))} in
    eq_rect_r (to_e_list (Cons a bes0)) _evar_0_ es0) bes es __

lfilled_pickable_rec_gen_measure :: (List Administrative_instruction) -> Nat
lfilled_pickable_rec_gen_measure lI =
  max0 lI
    (seq_administrative_instruction_rect' (\_ -> O) O (\_ -> O)
      (\_ _ lI2 _ m2 -> addn (S O) (max0 lI2 m2)) (\_ _ _ _ -> O) lI)

lfilledInd_pickable_rec_gen :: (Nat -> Lholed -> List
                               Administrative_instruction) -> ((List
                               Administrative_instruction) -> Lholed ->
                               Lholed -> Nat -> DecidableT LfilledInd) ->
                               (List Administrative_instruction) ->
                               PickableT2 Nat Lholed LfilledInd
lfilledInd_pickable_rec_gen fes d0 es' =
  pickableT2_equiv (\_ _ -> Pair (\x -> x) (\x -> x))
    (let {k = O} in
     ssr_have (lfilled_pickable_rec_gen_measure es') (\__top_assumption_ ->
       let {
        _evar_0_ = \m ->
         strong_rect (\m0 x fes0 d1 es'0 _ k0 ->
           ssr_have (\vs -> is_true_decidableT (const_list vs)) (\dcl ->
             ssr_have
               (ssr_have
                 (unsafeCoerce list_split_pickable3_gen es'0
                   (\vs es es'' _ ->
                   let {
                    _evar_0_ = \_ ->
                     decidableT_and (Inl __)
                       (decidableT_and (dcl vs)
                         (let {d = dcl vs} in
                          case d of {
                           Inl _ -> Inl
                            (let {_evar_0_ = LfilledBase vs es es''} in
                             eq_rect_r (cat vs (cat es es'')) _evar_0_ es'0);
                           Inr hNotConstVs -> Inr (\hLF ->
                            case hLF of {
                             LfilledBase vs0 es0 es'1 ->
                              eq_rec_r vs (\_ ->
                                eq_rec_r es'' (\_ ->
                                  eq_rec_r es (\_ ->
                                    eq_rect (cat vs (cat es es'')) (\_ ->
                                      hNotConstVs __) es'0) es0) es'1) vs0 __
                                __ __ __;
                             LfilledRec _ _ _ _ _ _ _ _ x0 ->
                              false_rect __ __ __ __ x0})}))}
                   in
                   let {
                    _evar_0_0 = \_ -> Inr (\__top_assumption_0 ->
                     let {
                      _evar_0_0 = \__top_assumption_1 ->
                       let {_evar_0_0 = \_ -> false_rec} in
                       case __top_assumption_1 of {
                        Pair _ x0 -> _evar_0_0 x0}}
                     in
                     case __top_assumption_0 of {
                      Pair _ x0 -> _evar_0_0 x0})}
                   in
                   case eq_op (seq_eqType administrative_instruction_eqType)
                          (unsafeCoerce es)
                          (unsafeCoerce fes0 k0 (LH_base vs es'')) of {
                    True -> _evar_0_ __;
                    False -> _evar_0_0 __})) (\__top_assumption_0 ->
                 let {
                  _evar_0_ = \__top_assumption_1 ->
                   let {
                    _evar_0_ = \__top_assumption_2 ->
                     let {
                      _evar_0_ = \__top_assumption_3 ->
                       let {
                        _evar_0_ = \vs es es'' __top_assumption_4 ->
                         let {
                          _evar_0_ = \__top_assumption_5 ->
                           let {
                            _evar_0_ = \__top_assumption_6 ->
                             let {
                              _evar_0_ = \i -> Inl (ExistT (Pair vs es'')
                               (eq_rect
                                 (lfilled_pickable_rec_gen_measure es'0)
                                 (\iH ->
                                 eq_rect_r (cat vs (cat es es'')) (\iH0 i0 ->
                                   eq_rect_r (fes0 k0 (LH_base vs es''))
                                     (\_ i1 -> Pair __ (Pair __ i1)) es iH0
                                     i0) es'0 iH i) m0 x))}
                             in
                             case __top_assumption_6 of {
                              Pair _ x0 -> _evar_0_ x0}}
                           in
                           case __top_assumption_5 of {
                            Pair _ x0 -> _evar_0_ x0}}
                         in
                         case __top_assumption_4 of {
                          Pair _ x0 -> _evar_0_ x0}}
                       in
                       case __top_assumption_3 of {
                        Pair x0 x1 -> _evar_0_ x0 x1}}
                     in
                     case __top_assumption_2 of {
                      Pair x0 x1 -> _evar_0_ x0 x1}}
                   in
                   case __top_assumption_1 of {
                    ExistT x0 x1 -> _evar_0_ x0 x1}}
                 in
                 let {
                  _evar_0_0 = \ex -> Inr (\__top_assumption_1 ->
                   let {
                    _evar_0_0 = \vs __top_assumption_2 ->
                     let {
                      _evar_0_0 = \es'' __top_assumption_3 ->
                       let {
                        _evar_0_0 = \__top_assumption_4 ->
                         let {
                          _evar_0_0 = \i ->
                           ex (ExistT vs (ExistT (fes0 k0 (LH_base vs es''))
                             (ExistT es'' (Pair __ (Pair __ (Pair __ i))))))}
                         in
                         case __top_assumption_4 of {
                          Pair _ x0 -> _evar_0_0 x0}}
                       in
                       case __top_assumption_3 of {
                        Pair _ x0 -> _evar_0_0 x0}}
                     in
                     case __top_assumption_2 of {
                      ExistT x0 x1 -> _evar_0_0 x0 x1}}
                   in
                   case __top_assumption_1 of {
                    ExistT x0 x1 -> _evar_0_0 x0 x1})}
                 in
                 case __top_assumption_0 of {
                  Inl x0 -> _evar_0_ x0;
                  Inr x0 -> _evar_0_0 x0})) (\p1 ->
               case p1 of {
                Inl __top_assumption_0 ->
                 let {
                  _evar_0_ = \__top_assumption_1 ->
                   let {
                    _evar_0_ = \vs es'' __top_assumption_2 ->
                     let {
                      _evar_0_ = \__top_assumption_3 ->
                       let {
                        _evar_0_ = \i -> Inl (ExistT (Pair O (LH_base vs
                         es''))
                         (eq_rect (lfilled_pickable_rec_gen_measure es'0)
                           (\iH ->
                           eq_rect_r
                             (cat vs (cat (fes0 k0 (LH_base vs es'')) es''))
                             (\_ _ _ ->
                             ssr_have __ (\_ ->
                               let {
                                _evar_0_ = LfilledBase vs
                                 (fes0 k0 (LH_base vs es'')) es''}
                               in
                               eq_rect_r k0 _evar_0_ (addn k0 O))) es'0 iH p1
                             i) m0 x))}
                       in
                       case __top_assumption_3 of {
                        Pair _ x0 -> _evar_0_ x0}}
                     in
                     case __top_assumption_2 of {
                      Pair _ x0 -> _evar_0_ x0}}
                   in
                   case __top_assumption_1 of {
                    Pair x0 x1 -> _evar_0_ x0 x1}}
                 in
                 case __top_assumption_0 of {
                  ExistT x0 x1 -> _evar_0_ x0 x1};
                Inr nE ->
                 ssr_have (\es'1 ->
                   ssr_have
                     (case es'1 of {
                       Nil -> Inr (\_ -> false_rec);
                       Cons __top_assumption_0 x0 ->
                        let {_evar_0_ = \_ _ -> Inr (\_ -> false_rec)} in
                        let {_evar_0_0 = \_ -> Inr (\_ -> false_rec)} in
                        let {_evar_0_1 = \_ _ -> Inr (\_ -> false_rec)} in
                        let {
                         _evar_0_2 = \n l1 l2 l3 -> Inl (ExistT (Pair (Pair
                          (Pair n l1) l2) l3) __)}
                        in
                        let {_evar_0_3 = \_ _ _ _ -> Inr (\_ -> false_rec)}
                        in
                        case __top_assumption_0 of {
                         AI_basic x1 -> _evar_0_ x1 x0;
                         AI_trap -> _evar_0_0 x0;
                         AI_invoke x1 -> _evar_0_1 x1 x0;
                         AI_label x1 x2 x3 ->
                          unsafeCoerce _evar_0_2 x1 x2 x3 x0;
                         AI_local x1 x2 x3 -> _evar_0_3 x1 x2 x3 x0}})
                     (\pparse ->
                     let {pparse0 = pickable4_weaken_T pparse} in
                     let {pparse1 = pickable3_weaken_T pparse0} in
                     let {pparse2 = pickable2_weaken_T pparse1} in
                     pickable_decidable_T pparse2)) (\dparse ->
                   let {
                    _evar_0_ = \__top_assumption_0 ->
                     let {
                      _evar_0_ = \__top_assumption_1 ->
                       let {
                        _evar_0_ = \vs es'' __top_assumption_2 ->
                         let {
                          _evar_0_ = \__top_assumption_3 ->
                           let {
                            _evar_0_ = \_ ->
                             case es'' of {
                              Nil -> false_rect;
                              Cons a x0 ->
                               case a of {
                                AI_label n es1 lI ->
                                 let {
                                  _evar_0_ = ssr_have __ (\_ ->
                                               let {
                                                fes' = \k1 lh ->
                                                 fes0 (addn k1 (S O)) (LH_rec
                                                   vs n es1 lh x0)}
                                               in
                                               ssr_have
                                                 (\_es'_ _lh_ _lh'_ _n0_ ->
                                                 d1 _es'_ _lh_ (LH_rec vs n
                                                   es1 _lh'_ x0)
                                                   (addn _n0_ (S O))) (\d2 ->
                                                 let {
                                                  __top_assumption_4 = 
                                                   x
                                                     (lfilled_pickable_rec_gen_measure
                                                       lI) __ fes' d2 lI __
                                                     k0}
                                                 in
                                                 let {
                                                  _evar_0_ = \__top_assumption_5 ->
                                                   let {
                                                    _evar_0_ = \__top_assumption_6 ->
                                                     let {
                                                      _evar_0_ = \n' lh lF ->
                                                       let {
                                                        lF0 = LfilledRec n'
                                                         vs n es1 lh x0
                                                         (fes' (addn k0 n')
                                                           lh) lI lF}
                                                       in
                                                       Inl (ExistT (Pair (S
                                                       n') (LH_rec vs n es1
                                                       lh x0))
                                                       (ssr_have __ (\_ ->
                                                         let {
                                                          _evar_0_ = \lF1 ->
                                                           lF1}
                                                         in
                                                         eq_rect_r
                                                           (addn k0 (S n'))
                                                           _evar_0_
                                                           (addn (addn k0 n')
                                                             (S O))) lF0))}
                                                     in
                                                     case __top_assumption_6 of {
                                                      Pair x1 x2 ->
                                                       _evar_0_ x1 x2}}
                                                   in
                                                   case __top_assumption_5 of {
                                                    ExistT x1 x2 ->
                                                     _evar_0_ x1 x2}}
                                                 in
                                                 let {
                                                  _evar_0_0 = \nP -> Inr
                                                   (\__top_assumption_5 ->
                                                   let {
                                                    _evar_0_0 = \n' __top_assumption_6 ->
                                                     let {
                                                      _evar_0_0 = \lh fI ->
                                                       nP
                                                         (case fI of {
                                                           LfilledBase vs0 es
                                                            es'1 ->
                                                            eq_rect O (\_ ->
                                                              eq_rect
                                                                (LH_base vs0
                                                                es'1) (\_ ->
                                                                eq_rect_r
                                                                  (fes0
                                                                    (addn k0
                                                                    O)
                                                                    (LH_base
                                                                    vs0
                                                                    es'1))
                                                                  (\_ ->
                                                                  eq_rect
                                                                    (cat vs0
                                                                    (cat
                                                                    (fes0
                                                                    (addn k0
                                                                    O)
                                                                    (LH_base
                                                                    vs0
                                                                    es'1))
                                                                    es'1))
                                                                    (\_ ->
                                                                    eq_rect
                                                                    (lfilled_pickable_rec_gen_measure
                                                                    es'0)
                                                                    (\iH _ ->
                                                                    eq_rect_r
                                                                    (cat vs
                                                                    (Cons
                                                                    (AI_label
                                                                    n es1 lI)
                                                                    x0))
                                                                    (\_ _ _ _ ->
                                                                    eq_rect O
                                                                    (\fI0 ->
                                                                    eq_rect
                                                                    (LH_base
                                                                    vs0 es'1)
                                                                    (\_ ->
                                                                    false_rect)
                                                                    lh fI0)
                                                                    n' fI)
                                                                    es'0 iH
                                                                    p1 nE __)
                                                                    m0 x __)
                                                                    (cat vs
                                                                    (Cons
                                                                    (AI_label
                                                                    n es1 lI)
                                                                    x0))) es)
                                                                lh) n' __ __
                                                              __ __;
                                                           LfilledRec k1 vs0
                                                            n0 es'1 lh' es''0
                                                            es lI0 x1 ->
                                                            eq_rect (S k1)
                                                              (\_ ->
                                                              eq_rect (LH_rec
                                                                vs0 n0 es'1
                                                                lh' es''0)
                                                                (\_ ->
                                                                eq_rect_r
                                                                  (fes0
                                                                    (addn k0
                                                                    (S k1))
                                                                    (LH_rec
                                                                    vs0 n0
                                                                    es'1 lh'
                                                                    es''0))
                                                                  (\_ ->
                                                                  eq_rect
                                                                    (cat vs0
                                                                    (Cons
                                                                    (AI_label
                                                                    n0 es'1
                                                                    lI0)
                                                                    es''0))
                                                                    (\_ x2 ->
                                                                    eq_rect
                                                                    (lfilled_pickable_rec_gen_measure
                                                                    es'0)
                                                                    (\iH _ ->
                                                                    eq_rect_r
                                                                    (cat vs
                                                                    (Cons
                                                                    (AI_label
                                                                    n es1 lI)
                                                                    x0))
                                                                    (\_ _ _ _ ->
                                                                    eq_rect
                                                                    (S k1)
                                                                    (\fI0 ->
                                                                    eq_rect
                                                                    (LH_rec
                                                                    vs0 n0
                                                                    es'1 lh'
                                                                    es''0)
                                                                    (\fI1 ->
                                                                    eq_rect_r
                                                                    n (\_ ->
                                                                    eq_rect_r
                                                                    es1
                                                                    (\_ ->
                                                                    eq_rect_r
                                                                    lI
                                                                    (eq_rect_r
                                                                    vs
                                                                    (\fI2 _ x3 ->
                                                                    eq_rect_r
                                                                    x0
                                                                    (\fI3 x4 ->
                                                                    eq_rect_r
                                                                    n
                                                                    (\fI4 x5 _ ->
                                                                    eq_rect_r
                                                                    es1
                                                                    (\_ x6 _ ->
                                                                    eq_rect_r
                                                                    lI
                                                                    (\x7 _ ->
                                                                    ExistT k1
                                                                    (ExistT
                                                                    lh'
                                                                    (ssr_have
                                                                    __ (\_ ->
                                                                    eq_rect_r
                                                                    (addn k0
                                                                    (S k1))
                                                                    x7
                                                                    (addn
                                                                    (addn k0
                                                                    k1) (S
                                                                    O))))))
                                                                    lI0 x6 __)
                                                                    es'1 fI4
                                                                    x5 __) n0
                                                                    fI3 x4 __)
                                                                    es''0 fI2
                                                                    x3) vs0
                                                                    fI1 __
                                                                    x2) lI0)
                                                                    es'1) n0
                                                                    __ __) lh
                                                                    fI0) n'
                                                                    fI) es'0
                                                                    iH p1 nE
                                                                    __) m0 x
                                                                    __)
                                                                    (cat vs
                                                                    (Cons
                                                                    (AI_label
                                                                    n es1 lI)
                                                                    x0))) es)
                                                                lh) n' __ __
                                                              __ __ x1})}
                                                     in
                                                     case __top_assumption_6 of {
                                                      ExistT x1 x2 ->
                                                       _evar_0_0 x1 x2}}
                                                   in
                                                   case __top_assumption_5 of {
                                                    ExistT x1 x2 ->
                                                     _evar_0_0 x1 x2})}
                                                 in
                                                 case __top_assumption_4 of {
                                                  Inl x1 -> _evar_0_ x1;
                                                  Inr x1 -> _evar_0_0 x1}))}
                                 in
                                 eq_rect_r
                                   (cat vs (Cons (AI_label n es1 lI) x0))
                                   _evar_0_ es'0;
                                _ -> false_rect}}}
                           in
                           case __top_assumption_3 of {
                            Pair _ x0 -> _evar_0_ x0}}
                         in
                         case __top_assumption_2 of {
                          Pair _ x0 -> _evar_0_ x0}}
                       in
                       case __top_assumption_1 of {
                        Pair x0 x1 -> _evar_0_ x0 x1}}
                     in
                     case __top_assumption_0 of {
                      ExistT x0 x1 -> _evar_0_ x0 x1}}
                   in
                   let {
                    _evar_0_0 = \nE' -> Inr (\__top_assumption_0 ->
                     let {
                      _evar_0_0 = \n __top_assumption_1 ->
                       let {
                        _evar_0_0 = \lh i ->
                         case i of {
                          LfilledBase vs es es'1 ->
                           eq_rect O (\_ ->
                             eq_rect (LH_base vs es'1) (\_ ->
                               eq_rec_r (fes0 (addn k0 O) (LH_base vs es'1))
                                 (\_ ->
                                 eq_rect
                                   (cat vs
                                     (cat
                                       (fes0 (addn k0 O) (LH_base vs es'1))
                                       es'1)) (\_ ->
                                   eq_rect
                                     (lfilled_pickable_rec_gen_measure es'0)
                                     (\iH ->
                                     eq_rect O (\i0 ->
                                       eq_rect (LH_base vs es'1) (\i1 ->
                                         eq_rect
                                           (cat vs
                                             (cat
                                               (fes0 (addn k0 O) (LH_base vs
                                                 es'1)) es'1))
                                           (\_ _ nE0 _ _ ->
                                           nE0 (ExistT vs (ExistT es'1
                                             (ssr_have __ (\_ ->
                                               let {
                                                _evar_0_0 = Pair __ (Pair __
                                                 (LfilledBase vs
                                                 (fes0 k0 (LH_base vs es'1))
                                                 es'1))}
                                               in
                                               eq_rect_r k0 _evar_0_0
                                                 (addn k0 O)))))) es'0 iH p1
                                           nE nE' i1) lh i0) n i) m0 x) es'0)
                                 es) lh) n __ __ __ __;
                          LfilledRec k1 vs n0 es'1 lh' es'' es lI x0 ->
                           eq_rect (S k1) (\_ ->
                             eq_rect (LH_rec vs n0 es'1 lh' es'') (\_ ->
                               eq_rect_r
                                 (fes0 (addn k0 (S k1)) (LH_rec vs n0 es'1
                                   lh' es'')) (\_ ->
                                 eq_rect
                                   (cat vs
                                     (cat (Cons (AI_label n0 es'1 lI) Nil)
                                       es'')) (\_ _ ->
                                   eq_rect
                                     (lfilled_pickable_rec_gen_measure es'0)
                                     (\iH ->
                                     eq_rect (S k1) (\i0 ->
                                       eq_rect (LH_rec vs n0 es'1 lh' es'')
                                         (\i1 ->
                                         eq_rect
                                           (cat vs
                                             (cat (Cons (AI_label n0 es'1 lI)
                                               Nil) es'')) (\_ _ _ nE'0 _ ->
                                           nE'0 (ExistT vs (ExistT
                                             (cat (Cons (AI_label n0 es'1 lI)
                                               Nil) es'') (Pair __ (Pair __
                                             (ExistT n0 (ExistT es'1 (ExistT
                                             lI (ExistT es'' __))))))))) es'0
                                           iH p1 nE nE' i1) lh i0) n i) m0 x)
                                   es'0) es) lh) n __ __ __ __ x0}}
                       in
                       case __top_assumption_1 of {
                        ExistT x0 x1 -> _evar_0_0 x0 x1}}
                     in
                     case __top_assumption_0 of {
                      ExistT x0 x1 -> _evar_0_0 x0 x1})}
                   in
                   case list_split_pickableT2 (\vs es ->
                          decidableT_and (dcl vs) (dparse es)) es'0 of {
                    Inl x0 -> unsafeCoerce _evar_0_ x0;
                    Inr x0 -> _evar_0_0 x0})}))) m fes d0 es' __ k}
       in
       unsafeCoerce _evar_0_ __top_assumption_))

lfilled_pickable_rec_gen :: (Nat -> Lholed -> List
                            Administrative_instruction) -> ((List
                            Administrative_instruction) -> Lholed -> Lholed
                            -> Nat -> DecidableT ()) -> (List
                            Administrative_instruction) -> PickableT2 
                            Nat Lholed ()
lfilled_pickable_rec_gen fes d0 es' =
  pickableT2_equiv (\n lh -> Pair __
    (let {es = fes (addn O n) lh} in
     case lfilled_Ind_Equivalent n lh es es' of {
      Pair x _ -> x}))
    (lfilledInd_pickable_rec_gen (\n lh -> fes (addn O n) lh)
      (\es'' lh lh' n0 ->
      decidableT_equiv
        (unsafeCoerce lfilled_Ind_Equivalent O lh (fes (addn O n0) lh') es'')
        (d0 es'' lh lh' (addn O n0))) es')

lfilled_decidable_base :: (List Administrative_instruction) -> (List
                          Administrative_instruction) -> Lholed -> DecidableT
                          ()
lfilled_decidable_base es es' lh =
  decidableT_equiv (Pair __
    (let {k = O} in
     case lfilled_Ind_Equivalent k lh es es' of {
      Pair x _ -> x}))
    (case lh of {
      LH_base vsh esh ->
       ssr_have
         (unsafeCoerce list_search_split_pickableT2
           administrative_instruction_eq_dec (\_l1_ _l2_ ->
           decidableT_and
             (decidable_decidableT
               (eq_comparable bool_eqType (unsafeCoerce const_list _l1_)
                 (unsafeCoerce True)))
             (decidableT_and_conj
               (decidable_decidableT
                 (eq_comparable
                   (seq_eqType administrative_instruction_eqType)
                   (unsafeCoerce _l1_) (unsafeCoerce vsh)))
               (decidable_decidableT
                 (eq_comparable
                   (seq_eqType administrative_instruction_eqType)
                   (unsafeCoerce _l2_) (unsafeCoerce esh))))) es es')
         (\__top_assumption_ ->
         let {
          _evar_0_ = \__top_assumption_0 ->
           let {
            _evar_0_ = \__top_assumption_1 ->
             let {
              _evar_0_ = \vs es'' -> Inl
               (eq_rect_r (cat vs (cat es es''))
                 (eq_rect_r vsh (\_ ->
                   eq_rect_r esh (LfilledBase vsh es esh) es'') vs __) es')}
             in
             (\_ -> case __top_assumption_1 of {
                     Pair x x0 -> _evar_0_ x x0})}
           in
           case __top_assumption_0 of {
            ExistT x x0 -> _evar_0_ x x0}}
         in
         let {
          _evar_0_0 = \nE -> Inr (\i ->
           nE
             (case i of {
               LfilledBase vs es0 es'0 ->
                eq_rect_r vsh (\_ ->
                  eq_rect_r esh (\_ ->
                    eq_rect_r es (\_ ->
                      eq_rect (cat vsh (cat es esh)) (\_ ->
                        eq_rect (cat vsh (cat es esh)) (\_ -> ExistT vsh
                          (ExistT esh __)) es' i) es') es0) es'0) vs __ __ __
                  __;
               LfilledRec _ _ _ _ _ _ _ _ x -> false_rect __ __ __ __ x}))}
         in
         case __top_assumption_ of {
          Inl x -> _evar_0_ x;
          Inr x -> _evar_0_0 x});
      LH_rec _ _ _ _ _ -> Inr (\i ->
       case i of {
        LfilledBase _ _ _ -> false_rec __ __ __;
        LfilledRec _ _ _ _ _ _ _ _ x -> false_rect __ __ __ __ x})})

lfilled_pickable_rec :: (List Administrative_instruction) -> ((List
                        Administrative_instruction) -> Lholed -> DecidableT
                        ()) -> (List Administrative_instruction) ->
                        PickableT2 Nat Lholed ()
lfilled_pickable_rec es d =
  lfilled_pickable_rec_gen (\_ _ -> es) (\es' lh _ _ -> d es' lh)

ety_a' :: Type -> (Store_record Sort) -> T_context -> (List
          Administrative_instruction) -> Function_type -> Es_is_basic ->
          Be_typing -> E_typing
ety_a' _ s c es ts _ hType =
  eq_rect (to_e_list (to_b_list es)) (Ety_a s c (to_b_list es) ts hType) es

bet_weakening_empty_both :: T_context -> (List Basic_instruction) ->
                            Result_type -> Be_typing -> Be_typing
bet_weakening_empty_both c es ts hType =
  let {x = Bet_weakening c es ts Nil Nil hType} in
  let {_evar_0_ = \x0 -> x0} in eq_rect_r ts _evar_0_ (cat ts Nil) x

et_to_bet :: Type -> (Store_record Sort) -> T_context -> (List
             Administrative_instruction) -> Function_type -> Es_is_basic ->
             E_typing -> Be_typing
et_to_bet host_function1 s c es ts hBasic hType =
  e_typing_rect host_function1 (\_ _ bes _ b _ ->
    eq_rect bes b (to_b_list (to_e_list bes)))
    (\_ c0 es0 e t1s t2s t3s _ iHHType1 _ iHHType2 hBasic0 ->
    let {hBasic1 = basic_concat es0 (Cons e Nil) hBasic0} in
    case hBasic1 of {
     Pair hBasic2 hBasic3 ->
      let {
       _evar_0_ = Bet_composition c0 (to_b_list es0) (to_b_single e) t1s t2s
        t3s (iHHType1 hBasic2) (iHHType2 hBasic3)}
      in
      eq_rect_r (cat (to_b_list es0) (to_b_list (Cons e Nil))) _evar_0_
        (to_b_list (cat es0 (Cons e Nil)))})
    (\_ c0 es0 ts0 t1s t2s _ iHHType hBasic0 -> Bet_weakening c0
    (to_b_list es0) ts0 t1s t2s (iHHType hBasic0)) (\_ _ _ _ -> false_rect)
    (\_ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ -> false_rect)
    (\_ _ _ _ _ _ _ _ _ _ _ _ _ -> false_rect) s c es ts hType hBasic

composition_typing_single :: T_context -> (List Basic_instruction) ->
                             Basic_instruction -> Result_type -> Result_type
                             -> Be_typing -> SigT (List Value_type)
                             (SigT (List Value_type)
                             (SigT (List Value_type)
                             (SigT Result_type
                             (Prod () (Prod () (Prod Be_typing Be_typing))))))
composition_typing_single c es1 e t1s t2s hType =
  let {tf = Tf t1s t2s} in
  ssr_have __ (\_ hType0 ->
    let {cat0 = cat es1 (Cons e Nil)} in
    ssr_have __ (\_ hType1 ->
      ssr_have __ (\_ hType2 ->
        be_typing_rect (\c0 v c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_const v) Nil) (\t2s0 t1s0 _ ->
              eq_rect Nil (\_ ->
                eq_rect (Cons (typeof v) Nil)
                  (eq_rect_r c1 (\_ ->
                    eq_rect Nil (\_ ->
                      eq_rect (Cons (typeof v) Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_const v) (\_ -> ExistT Nil (ExistT
                            Nil (ExistT (Cons (typeof v) Nil) (ExistT Nil
                            (Pair __ (Pair __ (Pair (Bet_empty c1) (Bet_const
                            c1 v)))))))) e0 __) es2 __) t2s0 __) t1s0 __) c0
                    __) t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 t op0 _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_unop t op0) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect (Cons t Nil)
                  (eq_rect_r c1 (\_ ->
                    eq_rect (Cons t Nil) (\_ ->
                      eq_rect (Cons t Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_unop t op0) (\_ -> ExistT Nil (ExistT
                            (Cons t Nil) (ExistT (Cons t Nil) (ExistT (Cons t
                            Nil) (Pair __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t Nil)
                              (Bet_empty c1)) (Bet_unop c1 t op0)))))))) e0
                            __) es2 __) t2s0 __) t1s0 __) c0 __) t2s0) t1s0
                __) (cat es2 (Cons e0 Nil))) c0) (\c0 t op0 _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_binop t op0) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t (Cons t Nil)) (\_ ->
                eq_rect (Cons t Nil)
                  (eq_rect_r c1 (\_ ->
                    eq_rect (Cons t (Cons t Nil)) (\_ ->
                      eq_rect (Cons t Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_binop t op0) (\_ -> ExistT Nil
                            (ExistT (Cons t (Cons t Nil)) (ExistT (Cons t
                            Nil) (ExistT (Cons t (Cons t Nil)) (Pair __ (Pair
                            __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t (Cons t
                              Nil)) (Bet_empty c1)) (Bet_binop c1 t
                            op0)))))))) e0 __) es2 __) t2s0 __) t1s0 __) c0
                    __) t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 t _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_testop t) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect (Cons T_i32 Nil)
                  (eq_rect_r c1 (\_ ->
                    eq_rect (Cons t Nil) (\_ ->
                      eq_rect (Cons T_i32 Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_testop t) (\_ -> ExistT Nil (ExistT
                            (Cons t Nil) (ExistT (Cons T_i32 Nil) (ExistT
                            (Cons t Nil) (Pair __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t Nil)
                              (Bet_empty c1)) (Bet_testop c1 t)))))))) e0 __)
                          es2 __) t2s0 __) t1s0 __) c0 __) t2s0) t1s0 __)
              (cat es2 (Cons e0 Nil))) c0) (\c0 t op0 _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_relop t op0) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t (Cons t Nil)) (\_ ->
                eq_rect (Cons T_i32 Nil)
                  (eq_rect_r c1 (\_ ->
                    eq_rect (Cons t (Cons t Nil)) (\_ ->
                      eq_rect (Cons T_i32 Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_relop t op0) (\_ -> ExistT Nil
                            (ExistT (Cons t (Cons t Nil)) (ExistT (Cons T_i32
                            Nil) (ExistT (Cons t (Cons t Nil)) (Pair __ (Pair
                            __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t (Cons t
                              Nil)) (Bet_empty c1)) (Bet_relop c1 t
                            op0)))))))) e0 __) es2 __) t2s0 __) t1s0 __) c0
                    __) t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 t1 t2 sx _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_cvtop t1 CVO_convert t2 sx) Nil)
              (\t2s0 t1s0 _ ->
              eq_rect (Cons t2 Nil) (\_ ->
                eq_rect (Cons t1 Nil)
                  (eq_rect_r c1 (\_ ->
                    eq_rect (Cons t2 Nil) (\_ ->
                      eq_rect (Cons t1 Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_cvtop t1 CVO_convert t2 sx) (\_ ->
                            ExistT Nil (ExistT (Cons t2 Nil) (ExistT (Cons t1
                            Nil) (ExistT (Cons t2 Nil) (Pair __ (Pair __
                            (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t2 Nil)
                              (Bet_empty c1)) (Bet_convert c1 t1 t2
                            sx)))))))) e0 __) es2 __) t2s0 __) t1s0 __) c0
                    __) t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 t1 t2 _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_cvtop t1 CVO_reinterpret t2 None) Nil)
              (\t2s0 t1s0 _ ->
              eq_rect (Cons t2 Nil) (\_ ->
                eq_rect (Cons t1 Nil)
                  (eq_rect_r c1 (\_ ->
                    eq_rect (Cons t2 Nil) (\_ ->
                      eq_rect (Cons t1 Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_cvtop t1 CVO_reinterpret t2 None)
                            (\_ -> ExistT Nil (ExistT (Cons t2 Nil) (ExistT
                            (Cons t1 Nil) (ExistT (Cons t2 Nil) (Pair __
                            (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t2 Nil)
                              (Bet_empty c1)) (Bet_reinterpret c1 t1
                            t2)))))))) e0 __) es2 __) t2s0 __) t1s0 __) c0
                    __) t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 ts ts' c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons BI_unreachable Nil) (\t2s0 t1s0 _ ->
              eq_rect_r t1s0 (\_ ->
                eq_rect_r t2s0
                  (eq_rect_r c1 (\_ ->
                    eq_rect_r t1s0 (\_ ->
                      eq_rect_r t2s0 (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r BI_unreachable (\_ -> ExistT Nil (ExistT
                            t1s0 (ExistT t2s0 (ExistT t1s0 (Pair __ (Pair __
                            (Pair
                            (bet_weakening_empty_both c1 Nil t1s0 (Bet_empty
                              c1)) (Bet_unreachable c1 t1s0 t2s0)))))))) e0
                            __) es2 __) ts' __) ts __) c0 __) ts') ts __)
              (cat es2 (Cons e0 Nil))) c0) (\c0 c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons BI_nop Nil) (\t2s0 t1s0 _ ->
              eq_rect Nil (\_ ->
                eq_rect Nil
                  (eq_rect_r c1 (\_ ->
                    eq_rect Nil (\_ ->
                      eq_rect Nil (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r BI_nop (\_ -> ExistT Nil (ExistT Nil
                            (ExistT Nil (ExistT Nil (Pair __ (Pair __ (Pair
                            (Bet_empty c1) (Bet_nop c1)))))))) e0 __) es2 __)
                        t2s0 __) t1s0 __) c0 __) t2s0) t1s0 __)
              (cat es2 (Cons e0 Nil))) c0) (\c0 t c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons BI_drop Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect Nil
                  (eq_rect_r c1 (\_ ->
                    eq_rect (Cons t Nil) (\_ ->
                      eq_rect Nil (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r BI_drop (\_ -> ExistT Nil (ExistT (Cons t
                            Nil) (ExistT Nil (ExistT (Cons t Nil) (Pair __
                            (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t Nil)
                              (Bet_empty c1)) (Bet_drop c1 t)))))))) e0 __)
                          es2 __) t2s0 __) t1s0 __) c0 __) t2s0) t1s0 __)
              (cat es2 (Cons e0 Nil))) c0) (\c0 t c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons BI_select Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t (Cons t (Cons T_i32 Nil))) (\_ ->
                eq_rect (Cons t Nil)
                  (eq_rect_r c1 (\_ ->
                    eq_rect (Cons t (Cons t (Cons T_i32 Nil))) (\_ ->
                      eq_rect (Cons t Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r BI_select (\_ -> ExistT Nil (ExistT (Cons
                            t (Cons t (Cons T_i32 Nil))) (ExistT (Cons t Nil)
                            (ExistT (Cons t (Cons t (Cons T_i32 Nil))) (Pair
                            __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t (Cons t
                              (Cons T_i32 Nil))) (Bet_empty c1)) (Bet_select
                            c1 t)))))))) e0 __) es2 __) t2s0 __) t1s0 __) c0
                    __) t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 tn tm es ->
          let {tf0 = Tf tn tm} in
          (\hType3 iHHType c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_block tf0 es) Nil) (\t2s0 t1s0 _ ->
              eq_rect_r t1s0 (\_ ->
                eq_rect_r t2s0
                  (eq_rect_r c1 (\hType4 iHHType0 _ ->
                    eq_rect_r t1s0 (\iHHType1 hType5 _ _ _ ->
                      eq_rect_r t2s0 (\_ ->
                        let {tf1 = Tf t1s0 t2s0} in
                        (\hType6 _ _ _ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_block tf1 es) (\_ -> ExistT Nil
                            (ExistT t1s0 (ExistT t2s0 (ExistT t1s0 (Pair __
                            (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil t1s0 (Bet_empty
                              c1)) (Bet_block c1 t1s0 t2s0 es hType6))))))))
                            e0 __) es2 __)) tm __ hType5 iHHType1 __ __) tn
                      iHHType0 hType4 __ __ __) c0 hType3 iHHType __) tm) tn
                __) (cat es2 (Cons e0 Nil))) c0))
          (\c0 tn tm es hType3 iHHType c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_loop (Tf tn tm) es) Nil) (\t2s0 t1s0 _ ->
              eq_rect_r t1s0 (\_ ->
                eq_rect_r t2s0
                  (eq_rect_r c1 (\hType4 iHHType0 _ ->
                    eq_rect_r t1s0 (\iHHType1 hType5 _ _ _ ->
                      eq_rect_r t2s0 (\_ hType6 _ _ _ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_loop (Tf t1s0 t2s0) es) (\_ -> ExistT
                            Nil (ExistT t1s0 (ExistT t2s0 (ExistT t1s0 (Pair
                            __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil t1s0 (Bet_empty
                              c1)) (Bet_loop c1 t1s0 t2s0 es hType6))))))))
                            e0 __) es2 __) tm __ hType5 iHHType1 __ __) tn
                      iHHType0 hType4 __ __ __) c0 hType3 iHHType __) tm) tn
                __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 tn tm es2 es3 hType3 iHHType1 hType4 iHHType2 c1 _ ->
          eq_rect_r c1 (\e0 es0 _ ->
            eq_rect (Cons (BI_if (Tf tn tm) es2 es3) Nil) (\t2s0 t1s0 _ ->
              eq_rect (app tn (Cons T_i32 Nil)) (\_ ->
                eq_rect_r t2s0
                  (eq_rect_r c1 (\hType5 hType6 iHHType3 iHHType4 _ ->
                    eq_rect (app tn (Cons T_i32 Nil)) (\_ ->
                      eq_rect_r t2s0 (\_ _ hType7 hType8 _ _ _ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_if (Tf tn t2s0) es2 es3) (\_ ->
                            ExistT Nil (ExistT (app tn (Cons T_i32 Nil))
                            (ExistT t2s0 (ExistT (app tn (Cons T_i32 Nil))
                            (Pair __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil
                              (app tn (Cons T_i32 Nil)) (Bet_empty c1))
                            (Bet_if_wasm c1 tn t2s0 es2 es3 hType8
                            hType7)))))))) e0 __) es0 __) tm iHHType4
                        iHHType3 hType6 hType5 __ __ __) t1s0 __) c0 hType3
                    hType4 iHHType1 iHHType2 __) tm) t1s0 __)
              (cat es0 (Cons e0 Nil))) c0) (\c0 i t1s0 ts t2s0 _ _ c1 _ ->
          let {
           x = \_ ->
            eq_rect_r c1 (\e0 es2 _ ->
              eq_rect (Cons (BI_br i) Nil) (\t2s1 t1s1 _ ->
                eq_rect (app t1s0 (unsafeCoerce ts)) (\_ ->
                  eq_rect_r t2s1
                    (eq_rect_r c1 (\_ _ _ ->
                      eq_rect (app t1s0 (unsafeCoerce ts)) (\_ ->
                        eq_rect_r t2s1 (\_ ->
                          eq_rect_r Nil (\_ ->
                            eq_rect_r (BI_br i) (\_ -> ExistT Nil (ExistT
                              (app t1s0 (unsafeCoerce ts)) (ExistT t2s1
                              (ExistT (app t1s0 (unsafeCoerce ts)) (Pair __
                              (Pair __ (Pair
                              (bet_weakening_empty_both c1 Nil
                                (app (unsafeCoerce t1s0) (unsafeCoerce ts))
                                (Bet_empty c1)) (Bet_br c1 i t1s0 ts
                              t2s1)))))))) e0 __) es2 __) t2s0 __) t1s1 __)
                      c0 __ __ __) t2s0) t1s1 __) (cat es2 (Cons e0 Nil))) c0}
          in
          unsafeCoerce x __) (\c0 i ts _ _ c1 _ ->
          let {
           x = \_ ->
            eq_rect_r c1 (\e0 es2 _ ->
              eq_rect (Cons (BI_br_if i) Nil) (\t2s0 t1s0 _ ->
                eq_rect (app (unsafeCoerce ts) (Cons T_i32 Nil)) (\_ ->
                  eq_rect_r t2s0
                    (eq_rect_r c1 (\_ _ _ ->
                      eq_rect (app (unsafeCoerce ts) (Cons T_i32 Nil)) (\_ ->
                        eq_rect_r t2s0 (\_ _ ->
                          eq_rect_r Nil (\_ ->
                            eq_rect_r (BI_br_if i) (\_ -> ExistT Nil (ExistT
                              (app (unsafeCoerce t2s0) (Cons T_i32 Nil))
                              (ExistT t2s0 (ExistT
                              (app (unsafeCoerce t2s0) (Cons T_i32 Nil))
                              (Pair __ (Pair __ (Pair
                              (bet_weakening_empty_both c1 Nil
                                (app (unsafeCoerce t2s0) (Cons T_i32 Nil))
                                (Bet_empty c1)) (Bet_br_if c1 i t2s0))))))))
                              e0 __) es2 __) ts __ __) t1s0 __) c0 __ __ __)
                    ts) t1s0 __) (cat es2 (Cons e0 Nil))) c0}
          in
          unsafeCoerce x __) (\c0 i ins ts t1s0 t2s0 _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_br_table ins i) Nil) (\t2s1 t1s1 _ ->
              eq_rect
                (app (unsafeCoerce t1s0)
                  (app (unsafeCoerce ts) (Cons T_i32 Nil))) (\_ ->
                eq_rect_r t2s1
                  (eq_rect_r c1 (\_ _ ->
                    eq_rect
                      (app (unsafeCoerce t1s0)
                        (app (unsafeCoerce ts) (Cons T_i32 Nil))) (\_ ->
                      eq_rect_r t2s1 (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_br_table ins i) (\_ -> ExistT Nil
                            (ExistT
                            (app (unsafeCoerce t1s0)
                              (app (unsafeCoerce ts) (Cons T_i32 Nil)))
                            (ExistT t2s1 (ExistT
                            (app (unsafeCoerce t1s0)
                              (app (unsafeCoerce ts) (Cons T_i32 Nil))) (Pair
                            __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil
                              (app (unsafeCoerce t1s0)
                                (app (unsafeCoerce ts) (Cons T_i32 Nil)))
                              (Bet_empty c1)) (Bet_br_table c1 i ins ts t1s0
                            t2s1)))))))) e0 __) es2 __) t2s0 __) t1s1 __) c0
                    __ __) t2s0) t1s1 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 ts t1s0 t2s0 _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons BI_return Nil) (\t2s1 t1s1 _ ->
              eq_rect (app t1s0 ts) (\_ ->
                eq_rect_r t2s1
                  (eq_rect_r c1 (\_ _ ->
                    eq_rect (app t1s0 ts) (\_ ->
                      eq_rect_r t2s1 (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r BI_return (\_ -> ExistT Nil (ExistT
                            (app t1s0 ts) (ExistT t2s1 (ExistT (app t1s0 ts)
                            (Pair __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (app t1s0 ts)
                              (Bet_empty c1)) (Bet_return c1 ts t1s0
                            t2s1)))))))) e0 __) es2 __) t2s0 __) t1s1 __) c0
                    __ __) t2s0) t1s1 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 i tf0 _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_call i) Nil) (\t2s0 t1s0 _ ->
              eq_rect_r (Tf t1s0 t2s0)
                (eq_rect_r c1 (\_ _ _ ->
                  eq_rect_r (Tf t1s0 t2s0) (\_ _ ->
                    eq_rect_r Nil (\_ ->
                      eq_rect_r (BI_call i) (\_ -> ExistT Nil (ExistT t1s0
                        (ExistT t2s0 (ExistT t1s0 (Pair __ (Pair __ (Pair
                        (bet_weakening_empty_both c1 Nil t1s0 (Bet_empty c1))
                        (Bet_call c1 i (Tf t1s0 t2s0))))))))) e0 __) es2 __)
                    tf0 __ __) c0 __ __ __) tf0) (cat es2 (Cons e0 Nil))) c0)
          (\c0 i t1s0 t2s0 _ _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_call_indirect i) Nil) (\t2s1 t1s1 _ ->
              eq_rect (app t1s0 (Cons T_i32 Nil)) (\_ ->
                eq_rect_r t2s1
                  (eq_rect_r c1 (\_ _ _ _ ->
                    eq_rect (app t1s0 (Cons T_i32 Nil)) (\_ ->
                      eq_rect_r t2s1 (\_ _ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_call_indirect i) (\_ -> ExistT Nil
                            (ExistT (app t1s0 (Cons T_i32 Nil)) (ExistT t2s1
                            (ExistT (app t1s0 (Cons T_i32 Nil)) (Pair __
                            (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil
                              (app t1s0 (Cons T_i32 Nil)) (Bet_empty c1))
                            (Bet_call_indirect c1 i t1s0 t2s1)))))))) e0 __)
                          es2 __) t2s0 __ __) t1s1 __) c0 __ __ __ __) t2s0)
                t1s1 __) (cat es2 (Cons e0 Nil))) c0) (\c0 i t _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_get_local i) Nil) (\t2s0 t1s0 _ ->
              eq_rect Nil (\_ ->
                eq_rect (Cons t Nil)
                  (eq_rect_r c1 (\_ _ _ ->
                    eq_rect Nil (\_ ->
                      eq_rect (Cons t Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_get_local i) (\_ -> ExistT Nil
                            (ExistT Nil (ExistT (Cons t Nil) (ExistT Nil
                            (Pair __ (Pair __ (Pair (Bet_empty c1)
                            (Bet_get_local c1 i t)))))))) e0 __) es2 __) t2s0
                        __) t1s0 __) c0 __ __ __) t2s0) t1s0 __)
              (cat es2 (Cons e0 Nil))) c0) (\c0 i t _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_set_local i) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect Nil
                  (eq_rect_r c1 (\_ _ _ ->
                    eq_rect (Cons t Nil) (\_ ->
                      eq_rect Nil (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_set_local i) (\_ -> ExistT Nil
                            (ExistT (Cons t Nil) (ExistT Nil (ExistT (Cons t
                            Nil) (Pair __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t Nil)
                              (Bet_empty c1)) (Bet_set_local c1 i t))))))))
                            e0 __) es2 __) t2s0 __) t1s0 __) c0 __ __ __)
                  t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 i t _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_tee_local i) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect (Cons t Nil)
                  (eq_rect_r c1 (\_ _ _ ->
                    eq_rect (Cons t Nil) (\_ ->
                      eq_rect (Cons t Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_tee_local i) (\_ -> ExistT Nil
                            (ExistT (Cons t Nil) (ExistT (Cons t Nil) (ExistT
                            (Cons t Nil) (Pair __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons t Nil)
                              (Bet_empty c1)) (Bet_tee_local c1 i t))))))))
                            e0 __) es2 __) t2s0 __) t1s0 __) c0 __ __ __)
                  t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 i t _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_get_global i) Nil) (\t2s0 t1s0 _ ->
              eq_rect Nil (\_ ->
                eq_rect (Cons t Nil)
                  (eq_rect_r c1 (\_ _ _ ->
                    eq_rect Nil (\_ ->
                      eq_rect (Cons t Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_get_global i) (\_ -> ExistT Nil
                            (ExistT Nil (ExistT (Cons t Nil) (ExistT Nil
                            (Pair __ (Pair __ (Pair (Bet_empty c1)
                            (Bet_get_global c1 i t)))))))) e0 __) es2 __)
                        t2s0 __) t1s0 __) c0 __ __ __) t2s0) t1s0 __)
              (cat es2 (Cons e0 Nil))) c0) (\c0 i g t _ _ _ _ c1 _ ->
          eq_rect_r c1 (\e1 es2 _ ->
            eq_rect (Cons (BI_set_global i) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect Nil
                  (eq_rect (tg_t g) (\_ _ ->
                    eq_rect_r c1 (\_ _ _ ->
                      eq_rect (Cons (tg_t g) Nil) (\_ ->
                        eq_rect Nil (\_ ->
                          eq_rect_r Nil (\_ ->
                            eq_rect_r (BI_set_global i) (\_ -> ExistT Nil
                              (ExistT (Cons (tg_t g) Nil) (ExistT Nil (ExistT
                              (Cons (tg_t g) Nil) (Pair __ (Pair __ (Pair
                              (bet_weakening_empty_both c1 Nil (Cons 
                                (tg_t g) Nil) (Bet_empty c1)) (Bet_set_global
                              c1 i g (tg_t g))))))))) e1 __) es2 __) t2s0 __)
                        t1s0 __) c0 __ __ __) t __ __) t2s0) t1s0 __)
              (cat es2 (Cons e1 Nil))) c0) (\c0 a off tp_sx t _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_load t tp_sx a off) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons T_i32 Nil) (\_ ->
                eq_rect (Cons t Nil)
                  (eq_rect_r c1 (\_ _ ->
                    eq_rect (Cons T_i32 Nil) (\_ ->
                      eq_rect (Cons t Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_load t tp_sx a off) (\_ -> ExistT Nil
                            (ExistT (Cons T_i32 Nil) (ExistT (Cons t Nil)
                            (ExistT (Cons T_i32 Nil) (Pair __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons T_i32 Nil)
                              (Bet_empty c1)) (Bet_load c1 a off tp_sx
                            t)))))))) e0 __) es2 __) t2s0 __) t1s0 __) c0 __
                    __) t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 a off tp t _ _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons (BI_store t tp a off) Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons T_i32 (Cons t Nil)) (\_ ->
                eq_rect Nil
                  (eq_rect_r c1 (\_ _ ->
                    eq_rect (Cons T_i32 (Cons t Nil)) (\_ ->
                      eq_rect Nil (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r (BI_store t tp a off) (\_ -> ExistT Nil
                            (ExistT (Cons T_i32 (Cons t Nil)) (ExistT Nil
                            (ExistT (Cons T_i32 (Cons t Nil)) (Pair __ (Pair
                            __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons T_i32
                              (Cons t Nil)) (Bet_empty c1)) (Bet_store c1 a
                            off tp t)))))))) e0 __) es2 __) t2s0 __) t1s0 __)
                    c0 __ __) t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons BI_current_memory Nil) (\t2s0 t1s0 _ ->
              eq_rect Nil (\_ ->
                eq_rect (Cons T_i32 Nil)
                  (eq_rect_r c1 (\_ _ ->
                    eq_rect Nil (\_ ->
                      eq_rect (Cons T_i32 Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r BI_current_memory (\_ -> ExistT Nil
                            (ExistT Nil (ExistT (Cons T_i32 Nil) (ExistT Nil
                            (Pair __ (Pair __ (Pair (Bet_empty c1)
                            (Bet_current_memory c1)))))))) e0 __) es2 __)
                        t2s0 __) t1s0 __) c0 __ __) t2s0) t1s0 __)
              (cat es2 (Cons e0 Nil))) c0) (\c0 _ c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect (Cons BI_grow_memory Nil) (\t2s0 t1s0 _ ->
              eq_rect (Cons T_i32 Nil) (\_ ->
                eq_rect (Cons T_i32 Nil)
                  (eq_rect_r c1 (\_ _ ->
                    eq_rect (Cons T_i32 Nil) (\_ ->
                      eq_rect (Cons T_i32 Nil) (\_ ->
                        eq_rect_r Nil (\_ ->
                          eq_rect_r BI_grow_memory (\_ -> ExistT Nil (ExistT
                            (Cons T_i32 Nil) (ExistT (Cons T_i32 Nil) (ExistT
                            (Cons T_i32 Nil) (Pair __ (Pair __ (Pair
                            (bet_weakening_empty_both c1 Nil (Cons T_i32 Nil)
                              (Bet_empty c1)) (Bet_grow_memory c1)))))))) e0
                            __) es2 __) t2s0 __) t1s0 __) c0 __ __) t2s0)
                t1s0 __) (cat es2 (Cons e0 Nil))) c0) (\c0 c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect Nil (\t2s0 t1s0 _ ->
              eq_rect Nil (\_ ->
                eq_rect Nil
                  (eq_rect_r c1 (\_ ->
                    eq_rect Nil (\_ ->
                      eq_rect Nil (\_ -> false_rect) t2s0 __) t1s0 __) c0 __)
                  t2s0) t1s0 __) (cat es2 (Cons e0 Nil))) c0)
          (\c0 es e0 t1s0 t2s0 t3s hType3 iHHType1 hType4 iHHType2 c1 _ ->
          eq_rect_r c1 (\e1 es2 _ ->
            eq_rect (app es (Cons e0 Nil)) (\t2s1 t1s1 _ ->
              eq_rect_r t1s1 (\_ ->
                eq_rect_r t2s1
                  (eq_rect_r c1 (\hType5 hType6 iHHType3 iHHType4 _ ->
                    eq_rect_r t1s1 (\iHHType5 hType7 _ ->
                      eq_rect_r t2s1 (\iHHType6 _ hType8 ->
                        eq_rect_r es2 (\_ hType9 _ ->
                          eq_rect_r e1 (\_ _ hType10 -> ExistT Nil (ExistT
                            t1s1 (ExistT t2s1 (ExistT t2s0 (Pair __ (Pair __
                            (Pair hType9 hType10))))))) e0 iHHType6 __ hType8)
                          es iHHType5 hType7 __) t3s iHHType4 __ hType6) t1s0
                      iHHType3 hType5 __) c0 hType3 hType4 iHHType1 iHHType2
                    __) t3s) t1s0 __) (cat es2 (Cons e1 Nil))) c0)
          (\c0 es ts t1s0 t2s0 hType3 iHHType c1 _ ->
          eq_rect_r c1 (\e0 es2 _ ->
            eq_rect_r (cat es2 (Cons e0 Nil)) (\t2s1 t1s1 _ ->
              eq_rect (app ts t1s0) (\_ ->
                eq_rect (app ts t2s0)
                  (eq_rect_r c1 (\hType4 iHHType0 _ ->
                    eq_rect_r (cat es2 (Cons e0 Nil)) (\iHHType1 hType5 _ ->
                      eq_rect (app ts t1s0) (\_ ->
                        eq_rect (app ts t2s0) (\_ ->
                          let {s = iHHType1 c1 __ e0 es2 __ t2s0 t1s0 __} in
                          case s of {
                           ExistT ts' s0 ->
                            case s0 of {
                             ExistT t1s' s1 ->
                              case s1 of {
                               ExistT t2s' s2 ->
                                case s2 of {
                                 ExistT t3s' h ->
                                  case h of {
                                   Pair _ x ->
                                    eq_rect_r (cat ts' t1s')
                                      (\hType6 iHHType2 p ->
                                      case p of {
                                       Pair _ x0 ->
                                        eq_rect_r (cat ts' t2s') (\_ _ p1 ->
                                          ExistT (cat ts ts') (ExistT t1s'
                                          (ExistT t2s' (ExistT t3s' (Pair __
                                          (Pair __ p1)))))) t2s0 iHHType2
                                          hType6 x0}) t1s0 hType5 iHHType1 x}}}}})
                          t2s1 __) t1s1 __) es iHHType0 hType4 __) c0 hType3
                    iHHType __) t2s1) t1s1 __) es) c0) c cat0 tf hType2 c __
          e es1 __ t2s t1s __) hType1) hType0) hType

composition_typing :: T_context -> (List Basic_instruction) -> (List
                      Basic_instruction) -> Result_type -> Result_type ->
                      Be_typing -> SigT (List Value_type)
                      (SigT (List Value_type)
                      (SigT (List Value_type)
                      (SigT Result_type
                      (Prod () (Prod () (Prod Be_typing Be_typing))))))
composition_typing c es1 es2 =
  let {es2' = rev0 es2} in
  eq_rect_r (rev0 es2')
    (list_rect (\es3 t1s t2s hType ->
      let {
       _evar_0_ = \hType0 -> ExistT Nil (ExistT t1s (ExistT t2s (ExistT t2s
        (Pair __ (Pair __ (Pair hType0
        (bet_weakening_empty_both c (rev0 Nil) t2s (Bet_empty c))))))))}
      in
      eq_rect_r es3 _evar_0_ (cat es3 Nil) hType)
      (\a es2'0 iHes2' es3 t1s t2s hType ->
      let {
       _evar_0_ = \hType0 ->
        let {
         _evar_0_ = \hType1 ->
          let {
           _evar_0_ = \hType2 ->
            let {
             hType3 = composition_typing_single c (cat es3 (rev0 es2'0)) a
                        t1s t2s hType2}
            in
            case hType3 of {
             ExistT ts' s ->
              case s of {
               ExistT t1s' s0 ->
                case s0 of {
                 ExistT t2s' s1 ->
                  case s1 of {
                   ExistT t3s' p ->
                    case p of {
                     Pair _ p1 ->
                      case p1 of {
                       Pair _ p2 ->
                        case p2 of {
                         Pair h3 h4 ->
                          eq_rect_r (cat ts' t1s')
                            (eq_rect_r (cat ts' t2s')
                              (let {h5 = iHes2' es3 t1s' t3s' h3} in
                               case h5 of {
                                ExistT ts2 s2 ->
                                 case s2 of {
                                  ExistT t1s2 s3 ->
                                   case s3 of {
                                    ExistT t2s2 s4 ->
                                     case s4 of {
                                      ExistT t3s2 p3 ->
                                       case p3 of {
                                        Pair _ p4 ->
                                         case p4 of {
                                          Pair _ p5 ->
                                           case p5 of {
                                            Pair h7 h8 ->
                                             eq_rect_r (cat ts2 t1s2)
                                               (eq_rect_r (cat ts2 t2s2)
                                                 (\h6 -> ExistT ts' (ExistT
                                                 (cat ts2 t1s2) (ExistT t2s'
                                                 (ExistT (cat ts2 t3s2) (Pair
                                                 __ (Pair __ (Pair
                                                 (Bet_weakening c es3 ts2
                                                 t1s2 t3s2 h7)
                                                 (let {
                                                   _evar_0_ = let {
                                                               _evar_0_ = Bet_composition
                                                                c
                                                                (rev0 es2'0)
                                                                a
                                                                (cat ts2
                                                                  t3s2)
                                                                (cat ts2
                                                                  t2s2) t2s'
                                                                (Bet_weakening
                                                                c
                                                                (rev0 es2'0)
                                                                ts2 t3s2 t2s2
                                                                h8) h6}
                                                              in
                                                              eq_rect
                                                                (cat
                                                                  (rev0
                                                                    es2'0)
                                                                  (Cons a
                                                                  Nil))
                                                                _evar_0_
                                                                (rcons
                                                                  (rev0
                                                                    es2'0) a)}
                                                  in
                                                  eq_rect_r
                                                    (rcons (rev0 es2'0) a)
                                                    _evar_0_
                                                    (rev0 (Cons a es2'0))))))))))
                                                 t3s' h4) t1s'}}}}}}}) t2s)
                            t1s}}}}}}}}
          in
          eq_rect_r (cat (cat es3 (rev0 es2'0)) (Cons a Nil)) _evar_0_
            (cat es3 (cat (rev0 es2'0) (Cons a Nil))) hType1}
        in
        eq_rect (cat (rev0 es2'0) (Cons a Nil)) _evar_0_
          (rcons (rev0 es2'0) a) hType0}
      in
      eq_rect_r (rcons (rev0 es2'0) a) _evar_0_ (rev0 (Cons a es2'0)) hType)
      es2') es2 es1

e_composition_typing_single :: Type -> (Store_record Sort) -> T_context ->
                               (List Administrative_instruction) ->
                               Administrative_instruction -> Result_type ->
                               Result_type -> E_typing -> SigT
                               (List Value_type)
                               (SigT (List Value_type)
                               (SigT (List Value_type)
                               (SigT Result_type
                               (Prod () (Prod () (Prod E_typing E_typing))))))
e_composition_typing_single host_function1 s c es1 es2 t1s t2s hType =
  let {tf = Tf t1s t2s} in
  ssr_have __ (\_ hType0 ->
    let {cat0 = cat es1 (Cons es2 Nil)} in
    ssr_have __ (\_ hType1 ->
      ssr_have __ (\_ hType2 ->
        ssr_have __ (\_ hType3 ->
          e_typing_rect host_function1 (\s0 c0 bes tf0 b s1 _ ->
            eq_rect_r s1 (\c1 _ ->
              eq_rect_r c1 (\es3 es4 _ ->
                eq_rect (to_e_list bes) (\t2s0 t1s0 _ ->
                  eq_rect_r (Tf t1s0 t2s0)
                    (eq_rect_r s1 (\_ ->
                      eq_rect_r c1 (\b0 _ ->
                        eq_rect_r (Tf t1s0 t2s0) (\b1 _ ->
                          let {ecat = b_e_elim bes (cat es4 (Cons es3 Nil))}
                          in
                          case ecat of {
                           Pair _ hbasic ->
                            eq_rect_r (to_b_list (cat es4 (Cons es3 Nil)))
                              (\b2 _ ->
                              let {
                               _evar_0_ = \b3 ->
                                let {
                                 b4 = composition_typing c1 (to_b_list es4)
                                        (to_b_list (Cons es3 Nil)) t1s0 t2s0
                                        b3}
                                in
                                let {
                                 hbasic0 = basic_concat es4 (Cons es3 Nil)
                                             hbasic}
                                in
                                case hbasic0 of {
                                 Pair e e0 ->
                                  case b4 of {
                                   ExistT ts' s2 ->
                                    case s2 of {
                                     ExistT t1s' s3 ->
                                      case s3 of {
                                       ExistT t2s' s4 ->
                                        case s4 of {
                                         ExistT t3s' p ->
                                          case p of {
                                           Pair _ p1 ->
                                            case p1 of {
                                             Pair _ p2 ->
                                              case p2 of {
                                               Pair h4 h5 ->
                                                eq_rect_r (cat ts' t1s')
                                                  (eq_rect_r (cat ts' t2s')
                                                    (ExistT ts' (ExistT t1s'
                                                    (ExistT t2s' (ExistT t3s'
                                                    (Pair __ (Pair __ (Pair
                                                    (ety_a' host_function1 s1
                                                      c1 es4 (Tf t1s' t3s') e
                                                      h4)
                                                    (ety_a' host_function1 s1
                                                      c1 (Cons es3 Nil) (Tf
                                                      t3s' t2s') e0 h5))))))))
                                                    t2s0) t1s0}}}}}}}}}
                              in
                              eq_rect_r
                                (cat (to_b_list es4)
                                  (to_b_list (Cons es3 Nil))) _evar_0_
                                (to_b_list (cat es4 (Cons es3 Nil))) b2) bes
                              b1 __}) tf0 b0 __) c0 b __) s0 __) tf0)
                  (cat es4 (Cons es3 Nil))) c0) s0)
            (\s0 c0 es e t1s0 t2s0 t3s hType4 iHHType1 hType5 iHHType2 s1 _ ->
            eq_rect_r s1 (\c1 _ ->
              eq_rect_r c1 (\es3 es4 _ ->
                eq_rect (cat es (Cons e Nil)) (\t2s1 t1s1 _ ->
                  eq_rect_r t1s1 (\_ ->
                    eq_rect_r t2s1
                      (eq_rect_r s1 (\hType6 hType7 iHHType3 iHHType4 _ ->
                        eq_rect_r c1 (\iHHType5 iHHType6 hType8 hType9 _ ->
                          eq_rect_r t1s1 (\hType10 iHHType7 _ ->
                            eq_rect_r t2s1 (\_ hType11 iHHType8 ->
                              eq_rect_r es4 (\hType12 _ _ ->
                                eq_rect_r es3 (\_ hType13 _ -> ExistT Nil
                                  (ExistT t1s1 (ExistT t2s1 (ExistT t2s0
                                  (Pair __ (Pair __ (Pair hType12
                                  hType13))))))) e __ hType11 iHHType8) es
                                hType10 iHHType7 __) t3s __ hType8 iHHType5)
                            t1s0 hType9 iHHType6 __) c0 iHHType4 iHHType3
                          hType7 hType6 __) s0 hType4 hType5 iHHType1
                        iHHType2 __) t3s) t1s0 __) (cat es4 (Cons es3 Nil)))
                c0) s0) (\s0 c0 es ts t1s0 t2s0 hType4 iHHType s1 _ ->
            eq_rect_r s1 (\c1 _ ->
              eq_rect_r c1 (\es3 es4 _ ->
                eq_rect_r (cat es4 (Cons es3 Nil)) (\t2s1 t1s1 _ ->
                  eq_rect (cat ts t1s0) (\_ ->
                    eq_rect (cat ts t2s0)
                      (eq_rect_r s1 (\hType5 iHHType0 _ ->
                        eq_rect_r c1 (\iHHType1 hType6 _ ->
                          eq_rect_r (cat es4 (Cons es3 Nil))
                            (\hType7 iHHType2 _ ->
                            eq_rect (cat ts t1s0) (\_ ->
                              eq_rect (cat ts t2s0) (\_ ->
                                let {
                                 s2 = iHHType2 s1 __ c1 __ es3 es4 __ t2s0
                                        t1s0 __}
                                in
                                case s2 of {
                                 ExistT x s3 ->
                                  case s3 of {
                                   ExistT t1s' s4 ->
                                    case s4 of {
                                     ExistT t2s' s5 ->
                                      case s5 of {
                                       ExistT t3s' p ->
                                        case p of {
                                         Pair _ p1 ->
                                          case p1 of {
                                           Pair _ p2 ->
                                            eq_rect_r (cat x t1s')
                                              (\iHHType3 hType8 ->
                                              eq_rect_r (cat x t2s') (\_ _ ->
                                                ExistT (cat ts x) (ExistT
                                                t1s' (ExistT t2s' (ExistT
                                                t3s' (Pair __ (Pair __
                                                p2)))))) t2s0 hType8 iHHType3)
                                              t1s0 iHHType2 hType7}}}}}})
                                t2s1 __) t1s1 __) es hType6 iHHType1 __) c0
                          iHHType0 hType5 __) s0 hType4 iHHType __) t2s1)
                    t1s1 __) es) c0) s0) (\s0 c0 tf0 s1 _ ->
            eq_rect_r s1 (\c1 _ ->
              eq_rect_r c1 (\es3 es4 _ ->
                eq_rect (Cons AI_trap Nil) (\t2s0 t1s0 _ ->
                  eq_rect_r (Tf t1s0 t2s0)
                    (eq_rect_r s1 (\_ ->
                      eq_rect_r c1 (\_ ->
                        eq_rect_r (Tf t1s0 t2s0) (\_ ->
                          eq_rect_r Nil (\_ ->
                            eq_rect_r AI_trap (\_ -> ExistT Nil (ExistT t1s0
                              (ExistT t2s0 (ExistT t1s0 (Pair __ (Pair __
                              (Pair
                              (ety_a' host_function1 s1 c1 Nil (Tf t1s0 t1s0)
                                __
                                (bet_weakening_empty_both c1 (to_b_list Nil)
                                  t1s0 (Bet_empty c1))) (Ety_trap s1 c1 (Tf
                              t1s0 t2s0))))))))) es3 __) es4 __) tf0 __) c0
                        __) s0 __) tf0) (cat es4 (Cons es3 Nil))) c0) s0)
            (\s0 c0 n f es ts s1 _ s2 _ ->
            eq_rect_r s2 (\c1 _ ->
              eq_rect_r c1 (\es3 es4 _ ->
                eq_rect (Cons (AI_local n f es) Nil) (\t2s0 t1s0 _ ->
                  eq_rect Nil (\_ ->
                    eq_rect_r t2s0
                      (eq_rect (length ts) (\_ _ ->
                        eq_rect_r s2 (\s3 _ ->
                          eq_rect_r c1 (\_ ->
                            eq_rect Nil (\_ ->
                              eq_rect_r t2s0 (\s4 _ _ _ ->
                                eq_rect_r Nil (\_ ->
                                  eq_rect_r (AI_local (length t2s0) f es)
                                    (\_ -> ExistT Nil (ExistT Nil (ExistT
                                    t2s0 (ExistT Nil (Pair __ (Pair __ (Pair
                                    (ety_a' host_function1 s2 c1 Nil (Tf Nil
                                      Nil) __ (Bet_empty c1)) (Ety_local s2
                                    c1 (length t2s0) f es t2s0 s4)))))))) es3
                                    __) es4 __) ts s3 __ __ __) t1s0 __) c0
                            __) s0 s1 __) n __ __) ts) t1s0 __)
                  (cat es4 (Cons es3 Nil))) c0) s0)
            (\s0 a c0 cl tf0 _ c1 s1 _ ->
            eq_rect_r s1 (\c2 _ ->
              eq_rect_r c2 (\es3 es4 _ ->
                eq_rect (Cons (AI_invoke a) Nil) (\t2s0 t1s0 _ ->
                  eq_rect_r (Tf t1s0 t2s0)
                    (eq_rect_r s1 (\_ c3 _ ->
                      eq_rect_r c2 (\_ ->
                        eq_rect_r (Tf t1s0 t2s0) (\c4 _ ->
                          eq_rect_r Nil (\_ ->
                            eq_rect_r (AI_invoke a) (\_ -> ExistT Nil (ExistT
                              t1s0 (ExistT t2s0 (ExistT t1s0 (Pair __ (Pair
                              __ (Pair
                              (ety_a' host_function1 s1 c2 Nil (Tf t1s0 t1s0)
                                __
                                (bet_weakening_empty_both c2 (to_b_list Nil)
                                  t1s0 (Bet_empty c2))) (Ety_invoke s1 a c2
                              cl (Tf t1s0 t2s0) c4)))))))) es3 __) es4 __)
                          tf0 c3 __) c0 __) s0 __ c1 __) tf0)
                  (cat es4 (Cons es3 Nil))) c0) s0)
            (\s0 c0 e0s es ts t2s0 n hType4 iHHType1 hType5 iHHType2 _ s1 _ ->
            eq_rect_r s1 (\c1 _ ->
              eq_rect_r c1 (\es3 es4 _ ->
                eq_rect (Cons (AI_label n e0s es) Nil) (\t2s1 t1s0 _ ->
                  eq_rect Nil (\_ ->
                    eq_rect_r t2s1
                      (eq_rect (length ts) (\_ _ ->
                        eq_rect_r s1 (\hType6 hType7 iHHType3 iHHType4 _ ->
                          eq_rect_r c1 (\iHHType5 iHHType6 hType8 hType9 _ ->
                            eq_rect Nil (\_ ->
                              eq_rect_r t2s1 (\hType10 hType11 _ _ _ ->
                                eq_rect_r Nil (\_ ->
                                  eq_rect_r (AI_label (length ts) e0s es)
                                    (\_ -> ExistT Nil (ExistT Nil (ExistT
                                    t2s1 (ExistT Nil (Pair __ (Pair __ (Pair
                                    (ety_a' host_function1 s1 c1 Nil (Tf Nil
                                      Nil) __ (Bet_empty c1)) (Ety_label s1
                                    c1 e0s es ts t2s1 (length ts) hType10
                                    hType11)))))))) es3 __) es4 __) t2s0
                                hType9 hType8 iHHType6 iHHType5 __) t1s0 __)
                            c0 iHHType4 iHHType3 hType7 hType6 __) s0 hType4
                          hType5 iHHType1 iHHType2 __) n __ __) t2s0) t1s0 __)
                  (cat es4 (Cons es3 Nil))) c0) s0) s c cat0 tf hType3 s __ c
            __ es2 es1 __ t2s t1s __) hType2) hType1) hType0) hType

e_composition_typing :: Type -> (Store_record Sort) -> T_context -> (List
                        Administrative_instruction) -> (List
                        Administrative_instruction) -> Result_type ->
                        Result_type -> E_typing -> SigT (List Value_type)
                        (SigT (List Value_type)
                        (SigT (List Value_type)
                        (SigT Result_type
                        (Prod () (Prod () (Prod E_typing E_typing))))))
e_composition_typing host_function1 s c es1 es2 =
  let {es2' = rev0 es2} in
  eq_rect_r (rev0 es2')
    (list_rect (\es3 t1s t2s hType ->
      let {
       _evar_0_ = \hType0 -> ExistT Nil (ExistT t1s (ExistT t2s (ExistT t2s
        (Pair __ (Pair __ (Pair hType0
        (ety_a' host_function1 s c (rev0 Nil) (Tf t2s t2s) __
          (bet_weakening_empty_both c Nil t2s (Bet_empty c)))))))))}
      in
      eq_rect_r es3 _evar_0_ (cat es3 Nil) hType)
      (\a es2'0 iHes2' es3 t1s t2s hType ->
      let {
       _evar_0_ = \hType0 ->
        let {
         _evar_0_ = \hType1 ->
          let {
           _evar_0_ = \hType2 ->
            let {
             hType3 = e_composition_typing_single host_function1 s c
                        (cat es3 (rev0 es2'0)) a t1s t2s hType2}
            in
            case hType3 of {
             ExistT ts' s0 ->
              case s0 of {
               ExistT t1s' s1 ->
                case s1 of {
                 ExistT t2s' s2 ->
                  case s2 of {
                   ExistT t3s' p ->
                    case p of {
                     Pair _ p1 ->
                      case p1 of {
                       Pair _ p2 ->
                        case p2 of {
                         Pair h3 h4 ->
                          eq_rect_r (cat ts' t1s')
                            (eq_rect_r (cat ts' t2s')
                              (let {h5 = iHes2' es3 t1s' t3s' h3} in
                               case h5 of {
                                ExistT ts2 s3 ->
                                 case s3 of {
                                  ExistT t1s2 s4 ->
                                   case s4 of {
                                    ExistT t2s2 s5 ->
                                     case s5 of {
                                      ExistT t3s2 p3 ->
                                       case p3 of {
                                        Pair _ p4 ->
                                         case p4 of {
                                          Pair _ p5 ->
                                           case p5 of {
                                            Pair h7 h8 ->
                                             eq_rect_r (cat ts2 t1s2)
                                               (eq_rect_r (cat ts2 t2s2)
                                                 (\h6 -> ExistT ts' (ExistT
                                                 (cat ts2 t1s2) (ExistT t2s'
                                                 (ExistT (cat ts2 t3s2) (Pair
                                                 __ (Pair __ (Pair
                                                 (Ety_weakening s c es3 ts2
                                                 t1s2 t3s2 h7)
                                                 (let {
                                                   _evar_0_ = let {
                                                               _evar_0_ = Ety_composition
                                                                s c
                                                                (rev0 es2'0)
                                                                a
                                                                (cat ts2
                                                                  t3s2)
                                                                (cat ts2
                                                                  t2s2) t2s'
                                                                (Ety_weakening
                                                                s c
                                                                (rev0 es2'0)
                                                                ts2 t3s2 t2s2
                                                                h8) h6}
                                                              in
                                                              eq_rect
                                                                (cat
                                                                  (rev0
                                                                    es2'0)
                                                                  (Cons a
                                                                  Nil))
                                                                _evar_0_
                                                                (rcons
                                                                  (rev0
                                                                    es2'0) a)}
                                                  in
                                                  eq_rect_r
                                                    (rcons (rev0 es2'0) a)
                                                    _evar_0_
                                                    (rev0 (Cons a es2'0))))))))))
                                                 t3s' h4) t1s'}}}}}}}) t2s)
                            t1s}}}}}}}}
          in
          eq_rect_r (cat (cat es3 (rev0 es2'0)) (Cons a Nil)) _evar_0_
            (cat es3 (cat (rev0 es2'0) (Cons a Nil))) hType1}
        in
        eq_rect (cat (rev0 es2'0) (Cons a Nil)) _evar_0_
          (rcons (rev0 es2'0) a) hType0}
      in
      eq_rect_r (rcons (rev0 es2'0) a) _evar_0_ (rev0 (Cons a es2'0)) hType)
      es2') es2 es1

break_typing :: Type -> Host -> Immediate -> T_context -> Result_type ->
                Result_type -> Be_typing -> SigT Sort (SigT (List Sort) ())
break_typing _ host_instance1 n c t1s t2s hType =
  let {gen_x = Cons (BI_br n) Nil} in
  let {gen_x0 = Tf t1s t2s} in
  be_typing_rect (\_ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ -> false_rect)
    (\_ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ _ _ -> false_rect)
    (\_ _ _ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    false_rect) (\_ i t1s0 ts t2s0 _ _ host_instance2 n0 t1s1 t2s1 _ ->
    solution_left n0 (\t1s2 ts0 t2s2 _ _ host_instance3 t1s3 t2s3 _ ->
      solution_left t2s3 (\_ _ _ t1s4 _ ->
        solution_right (app (unsafeCoerce t1s2) (unsafeCoerce ts0)) (ExistT
          ts0 (ExistT t1s2 __)) t1s4) t2s2 __ __ host_instance3 t1s3 __) i
      t1s0 ts t2s0 __ __ host_instance2 t1s1 t2s1) (\_ _ _ _ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ _ _ _ _ _ _ -> false_rect)
    (\_ _ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ _ -> false_rect)
    (\_ _ _ _ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ _ _ _ _ -> false_rect)
    (\_ _ _ _ _ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ _ ->
    false_rect) (\_ _ _ _ _ _ _ -> false_rect) (\_ _ _ _ _ _ -> false_rect)
    (\_ es e t1s0 t2s0 t3s hType1 iHHType1 hType2 iHHType2 host_instance2 n0 t1s1 t2s1 _ _ ->
    solution_left t2s1
      (\hType3 hType4 iHHType3 iHHType4 host_instance3 n1 t1s2 _ _ ->
      solution_left t1s2
        (\t2s2 t2s3 hType5 hType6 iHHType5 iHHType6 host_instance4 n2 _ ->
        eq_rect_r Nil (\_ iHHType7 ->
          eq_rect_r (BI_br n2) (\_ iHHType8 ->
            eq_rect_r t2s2 (\_ -> iHHType8 host_instance4 n2 t2s2 t2s3 __ __)
              t1s2 iHHType7) e hType6 iHHType6) es hType5 iHHType5) t1s0 t2s0
        t2s1 hType3 hType4 iHHType3 iHHType4 host_instance3 n1 __) t3s hType1
      hType2 iHHType1 iHHType2 host_instance2 n0 t1s1 __ __)
    (\_ es ts t1s0 t2s0 hType0 iHHType host_instance2 n0 t1s1 t2s1 _ ->
    solution_left (Cons (BI_br n0) Nil)
      (\ts0 t1s2 t2s2 hType1 iHHType0 host_instance3 t1s3 t2s3 _ ->
      solution_right (app ts0 t2s2) (\_ ->
        solution_right (app ts0 t1s2)
          (let {s = iHHType0 host_instance3 n0 t1s2 t2s2 __ __} in
           case s of {
            ExistT x h ->
             case h of {
              ExistT ts1 _ ->
               eq_rect_r (cat (unsafeCoerce ts1) (unsafeCoerce x)) (\_ _ ->
                 ExistT x (ExistT (cat (unsafeCoerce ts0) ts1) __)) t1s2
                 hType1 iHHType0}}) t1s3) t2s3 __) es ts t1s0 t2s0 hType0
      iHHType host_instance2 t1s1 t2s1) c gen_x gen_x0 hType host_instance1 n
    t1s t2s __ __

label_typing :: Type -> (Store_record Sort) -> T_context -> Nat -> (List
                Administrative_instruction) -> (List
                Administrative_instruction) -> Result_type -> Result_type ->
                E_typing -> SigT Result_type
                (SigT (List Value_type)
                (Prod () (Prod E_typing (Prod E_typing ()))))
label_typing host_function1 s c n es0 es ts1 ts2 hType =
  let {es2 = Cons (AI_label n es0 es) Nil} in
  let {tf2 = Tf ts1 ts2} in
  e_typing_rect host_function1 (\s0 c0 bes tf b _ ts3 ts4 c1 s1 _ _ _ ->
    eq_rect_r (Tf ts4 ts3) (\b0 ->
      eq_rect_r c1 (\_ ->
        eq_rect_r s1
          (let {h = to_e_list_basic bes} in
           let {_evar_0_ = \_ -> false_rect} in
           eq_rect_r (Cons (AI_label n es0 es) Nil) (unsafeCoerce _evar_0_)
             (to_e_list bes) h) s0) c0 b0) tf b)
    (\s0 c0 es1 e t1s t2s _ hType1 iHHType1 hType2 iHHType2 _ ts3 ts4 c1 s1 _ _ _ ->
    eq_rect_r c1 (\hType3 hType4 iHHType3 iHHType4 ->
      eq_rect_r s1 (\iHHType5 iHHType6 hType5 hType6 ->
        eq_rect_r Nil (\_ iHHType7 ->
          eq_rect_r (AI_label n es0 es) (\_ iHHType8 ->
            eq_rect_r t2s (\_ _ -> iHHType8 __ ts3 ts4 c1 s1 __ __ __) t1s
              iHHType7 __) e hType5 iHHType5) es1 hType6 iHHType6) s0
        iHHType4 iHHType3 hType4 hType3) c0 hType1 hType2 iHHType1 iHHType2)
    (\s0 c0 es1 ts t1s t2s hType0 iHHType _ ts3 ts4 c1 s1 _ _ _ ->
    eq_rect_r (Cons (AI_label n es0 es) Nil) (\hType1 iHHType0 ->
      eq_rect_r c1 (\iHHType1 hType2 ->
        eq_rect_r s1 (\hType3 iHHType2 ->
          let {s2 = iHHType2 __ t2s t1s c1 s1 __ __ __} in
          case s2 of {
           ExistT x h ->
            eq_rect (cat ts t1s) (\_ ->
              eq_rect (cat ts t2s)
                (eq_rect (cat ts t1s) (\_ ->
                  eq_rect (cat ts t2s) (\_ ->
                    case h of {
                     ExistT ts2' p ->
                      case p of {
                       Pair _ p1 ->
                        case p1 of {
                         Pair h2 p2 ->
                          case p2 of {
                           Pair h3 _ ->
                            eq_rect_r (cat t1s ts2') (\iHHType3 hType4 _ ->
                              eq_rect (length x) (\_ _ -> ExistT x (ExistT
                                ts2'
                                (let {
                                  _evar_0_ = Pair __ (Pair h2 (Pair h3 __))}
                                 in
                                 eq_rect_r (cat (cat ts t1s) ts2') _evar_0_
                                   (cat ts (cat t1s ts2'))))) n hType4
                                iHHType3) t2s iHHType2 hType3 __}}}}) ts3 __)
                  ts4 __) ts3) ts4 __}) s0 hType2 iHHType1) c0 iHHType0
        hType1) es1 hType0 iHHType) (\s0 c0 _ _ _ _ c1 s1 _ _ _ ->
    eq_rect_r c1 (eq_rect_r s1 false_rect s0) c0)
    (\s0 c0 n0 _ _ ts s1 _ _ _ _ c1 s2 _ _ _ ->
    eq_rect (length ts) (\_ ->
      eq_rect_r c1 (eq_rect_r s2 (\_ -> false_rect) s0 s1) c0) n0 __)
    (\s0 _ c0 _ tf _ c1 _ ts3 ts4 c2 s1 _ _ _ ->
    eq_rect_r (Tf ts4 ts3) (\c3 ->
      eq_rect_r c2 (eq_rect_r s1 (\_ _ -> false_rect) s0 __ c3) c0) tf c1)
    (\s0 c0 e0s es1 ts t2s n0 hType1 iHHType1 hType2 iHHType2 _ _ ts3 ts4 c1 s1 _ _ _ ->
    eq_rect (length ts) (\_ ->
      eq_rect_r c1 (\hType3 hType4 iHHType3 iHHType4 ->
        eq_rect_r s1 (\iHHType5 iHHType6 hType5 hType6 ->
          eq_rect (length ts) (\_ ->
            eq_rect_r es0 (\_ ->
              eq_rect_r es
                (eq_rect Nil (\_ ->
                  eq_rect_r ts3
                    (eq_rect (length ts) (\_ iHHType7 iHHType8 ->
                      eq_rect_r es0 (\_ hType7 iHHType9 ->
                        eq_rect_r es (\_ hType8 iHHType10 ->
                          eq_rect Nil (\_ ->
                            eq_rect_r ts3 (\hType9 _ hType10 _ _ -> ExistT ts
                              (ExistT ts3 (Pair __ (Pair hType9 (Pair hType10
                              __))))) t2s hType7 iHHType10 hType8 iHHType9 __)
                            ts4 __) es1 __ hType5 iHHType8) e0s __ hType6
                        iHHType7) n __ iHHType6 iHHType5) t2s) ts4 __) es1)
              e0s) n __ __) s0 iHHType4 iHHType3 hType4 hType3) c0 hType1
        hType2 iHHType1 iHHType2) n0 __) s c es2 tf2 hType __ ts2 ts1 c s __
    __ __

return_typing :: Type -> Host -> T_context -> Result_type -> Result_type ->
                 Be_typing -> SigT (List Value_type)
                 (SigT (List Value_type) ())
return_typing _ host_instance1 c t1s t2s hType =
  let {gen_x = Cons BI_return Nil} in
  let {gen_x0 = Tf t1s t2s} in
  be_typing_rect (\_ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ ->
    false_rec) (\_ _ _ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ _ _ ->
    false_rec) (\_ _ _ _ _ _ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ _ _ _ -> false_rec)
    (\_ ts t1s0 t2s0 _ host_instance2 t1s1 t2s1 _ _ ->
    solution_left t2s1 (\_ _ t1s2 _ ->
      solution_right (app t1s0 ts) (ExistT ts (ExistT t1s0 __)) t1s2) t2s0 __
      host_instance2 t1s1 __) (\_ _ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ _ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ _ _ _ _ _ ->
    false_rec) (\_ _ _ _ _ _ -> false_rec) (\_ _ _ _ _ _ -> false_rec)
    (\_ _ _ _ _ -> false_rec)
    (\_ es e t1s0 t2s0 t3s hType1 iHHType1 hType2 iHHType2 host_instance2 t1s1 t2s1 _ _ ->
    solution_left t2s1
      (\hType3 hType4 iHHType3 iHHType4 host_instance3 t1s2 _ _ ->
      solution_left t1s2
        (\t2s2 t2s3 hType5 hType6 iHHType5 iHHType6 host_instance4 _ ->
        eq_rect_r Nil (\_ iHHType7 ->
          eq_rect_r BI_return (\_ iHHType8 ->
            eq_rect_r t2s2 (\_ -> iHHType8 host_instance4 t2s2 t2s3 __ __)
              t1s2 iHHType7) e hType6 iHHType6) es hType5 iHHType5) t1s0 t2s0
        t2s1 hType3 hType4 iHHType3 iHHType4 host_instance3 __) t3s hType1
      hType2 iHHType1 iHHType2 host_instance2 t1s1 __ __)
    (\_ es ts t1s0 t2s0 hType0 iHHType host_instance2 t1s1 t2s1 _ ->
    solution_left (Cons BI_return Nil)
      (\ts0 t1s2 t2s2 hType1 iHHType0 host_instance3 t1s3 t2s3 _ ->
      solution_right (app ts0 t2s2) (\_ ->
        solution_right (app ts0 t1s2)
          (let {s = iHHType0 host_instance3 t1s2 t2s2 __ __} in
           case s of {
            ExistT ts' iHHType' ->
             case iHHType' of {
              ExistT ts'' _ ->
               eq_rect_r (cat ts'' ts') (\_ _ -> ExistT ts' (ExistT
                 (cat ts0 ts'') __)) t1s2 hType1 iHHType0}}) t1s3) t2s3 __)
      es ts t1s0 t2s0 hType0 iHHType host_instance2 t1s1 t2s1) c gen_x gen_x0
    hType host_instance1 t1s t2s __ __

type Terminal_form = Sumbool

reduce_trap_left :: (List Administrative_instruction) -> Reduce_simple
reduce_trap_left vs =
  case vs of {
   Nil -> false_rect;
   Cons a vs0 -> Rs_trap (Cons a (cat vs0 (Cons AI_trap Nil))) (LH_base (Cons
    a vs0) Nil)}

reduce_composition :: Type -> Host -> (Store_record Sort) -> (List
                      Administrative_instruction) -> Frame -> (List
                      Administrative_instruction) -> (List
                      Administrative_instruction) -> (Store_record Sort) ->
                      Frame -> (List Administrative_instruction) -> Sort ->
                      Sort -> Reduce -> Reduce
reduce_composition _ _ s cs f es es0 s' f' es' hs hs' x =
  R_label s f es (cat cs (cat es es0)) s' f' es' (cat cs (cat es' es0)) O
    (LH_base cs es0) hs hs' x

reduce_composition_right :: Type -> Host -> (Store_record Sort) -> Frame ->
                            (List Administrative_instruction) -> (List
                            Administrative_instruction) -> (Store_record
                            Sort) -> Frame -> (List
                            Administrative_instruction) -> Sort -> Sort ->
                            Reduce -> Reduce
reduce_composition_right host_function1 host_instance1 s f es es0 s' f' es' hs hs' hReduce =
  reduce_composition host_function1 host_instance1 s Nil f es es0 s' f' es'
    hs hs' hReduce

reduce_composition_left :: Type -> Host -> (Store_record Sort) -> (List
                           Administrative_instruction) -> Frame -> (List
                           Administrative_instruction) -> (Store_record 
                           Sort) -> Frame -> (List
                           Administrative_instruction) -> Sort -> Sort ->
                           Reduce -> Reduce
reduce_composition_left host_function1 host_instance1 s cs f es s' f' es' hs hs' x =
  let {
   hReduce = reduce_composition host_function1 host_instance1 s cs f es Nil
               s' f' es' hs hs' x}
  in
  let {
   _evar_0_ = \hReduce0 ->
    let {_evar_0_ = \hReduce1 -> hReduce1} in
    eq_rect_r es' _evar_0_ (cat es' Nil) hReduce0}
  in
  eq_rect_r es _evar_0_ (cat es Nil) hReduce

terminal_form_v_e :: (List Administrative_instruction) -> (List
                     Administrative_instruction) -> Terminal_form ->
                     Terminal_form
terminal_form_v_e vs es hTerm =
  case hTerm of {
   Left -> Left;
   Right ->
    case vs of {
     Nil -> eq_rec_r (Cons AI_trap Nil) Right es;
     Cons a vs0 ->
      case vs0 of {
       Nil ->
        case es of {
         Nil ->
          eq_rec_r AI_trap (eq_rec_r AI_trap (\_ _ -> false_rec) a __ __) a;
         Cons _ _ -> false_rec};
       Cons _ _ -> false_rec}}}

terminal_trap :: Terminal_form
terminal_trap =
  Right

typeof_append :: (List Value_type) -> Value_type -> (List Value) -> SigT
                 Value ()
typeof_append ts t vs =
  let {
   _evar_0_ = \_ ->
    let {
     _evar_0_ = \_ ->
      let {l = drop (size0 ts) vs} in
      case l of {
       Nil -> false_rect;
       Cons v l0 ->
        case l0 of {
         Nil ->
          eq_rect_r (typeof v)
            (eq_rect_r (typeof v) (\_ -> ExistT v __) t __) t;
         Cons _ _ -> false_rect}}}
    in
    eq_rect (map0 typeof (drop (size0 ts) vs)) _evar_0_
      (drop (size0 ts) (map0 typeof vs)) __}
  in
  eq_rect (map0 typeof (take (size0 ts) vs)) _evar_0_
    (take (size0 ts) (map0 typeof vs)) __

nth_error_map :: (List a1) -> Nat -> (a1 -> a2) -> a2 -> SigT a1 ()
nth_error_map l n f fx =
  nat_rect (\l0 f0 fx0 _ ->
    case l0 of {
     Nil -> false_rect;
     Cons x _ ->
      eq_rect (f0 x) (eq_rect (f0 x) (\_ -> ExistT x __) fx0 __) fx0})
    (\_ iHn l0 f0 fx0 _ ->
    case l0 of {
     Nil -> false_rect;
     Cons _ l1 -> iHn l1 f0 fx0 __}) n l f fx __

func_context_store :: Type -> (Store_record Sort) -> Instance -> T_context ->
                      Nat -> Function_type -> SigT Funcaddr ()
func_context_store _ _ i c j _ =
  case i of {
   Build_instance _ inst_funcs _ _ _ ->
    case c of {
     Build_t_context _ tc_func_t0 _ _ _ tc_local0 tc_label0 tc_return0 ->
      case tc_local0 of {
       Nil ->
        case tc_label0 of {
         Nil ->
          case tc_return0 of {
           Some _ -> false_rec;
           None ->
            let {
             _evar_0_ = \_ ->
              let {
               _evar_0_ = \_ ->
                let {
                 _evar_0_ = \_ ->
                  let {o = nth_error inst_funcs j} in
                  case o of {
                   Some f -> ExistT f __;
                   None -> false_rec}}
                in
                eq_rect (length inst_funcs) _evar_0_ (length tc_func_t0) __}
              in
              eq_rect (length tc_func_t0) _evar_0_ (size0 tc_func_t0) __}
            in
            eq_rect (length inst_funcs) _evar_0_ (size0 inst_funcs) __};
         Cons _ _ -> false_rec};
       Cons _ _ -> false_rec}}}

mem_context_store :: Type -> (Store_record Sort) -> Instance -> T_context ->
                     SigT Nat ()
mem_context_store _ _ i c =
  case i of {
   Build_instance _ _ _ inst_memory _ ->
    case c of {
     Build_t_context _ _ _ _ _ tc_local0 tc_label0 tc_return0 ->
      case tc_local0 of {
       Nil ->
        case tc_label0 of {
         Nil ->
          case tc_return0 of {
           Some _ -> false_rec;
           None ->
            case inst_memory of {
             Nil -> false_rec;
             Cons m _ -> ExistT m __}};
         Cons _ _ -> false_rec};
       Cons _ _ -> false_rec}}}

store_typing_stabaddr :: Type -> (Store_record Sort) -> Frame -> T_context ->
                         Nat -> Nat -> Store_typing -> SigT
                         (Function_closure Sort) ()
store_typing_stabaddr _ s f c c0 a _ =
  case s of {
   Build_store_record s_funcs0 s_tables0 s_mems0 s_globals0 ->
    let {i = f_inst f} in
    case i of {
     Build_instance _ _ inst_tab0 _ _ ->
      case c of {
       Build_t_context _ _ _ tc_table0 _ tc_local0 tc_label0 tc_return0 ->
        case tc_local0 of {
         Nil ->
          case tc_label0 of {
           Nil ->
            case tc_return0 of {
             Some _ -> false_rect;
             None ->
              case inst_tab0 of {
               Nil -> false_rect;
               Cons t _ ->
                let {
                 o = case nth_error
                            (s_tables (Build_store_record s_funcs0 s_tables0
                              s_mems0 s_globals0)) t of {
                      Some y -> nth_error (table_data y) c0;
                      None -> None}}
                in
                case o of {
                 Some f0 ->
                  let {
                   o0 = nth_error
                          (s_tables (Build_store_record s_funcs0 s_tables0
                            s_mems0 s_globals0)) t}
                  in
                  case o0 of {
                   Some _ ->
                    eq_rect_r (Some a) (\_ ->
                      case tc_table0 of {
                       Nil -> false_rect;
                       Cons _ _ ->
                        let {o1 = nth_error s_funcs0 a} in
                        case o1 of {
                         Some f1 -> ExistT f1 __;
                         None -> false_rect}}) f0 __;
                   None -> false_rect};
                 None -> false_rect}}};
           Cons _ _ -> false_rect};
         Cons _ _ -> false_rect}}}}

t_progress_be :: Type -> Host -> T_context -> (List Basic_instruction) ->
                 Result_type -> Result_type -> (List Value) -> (List
                 (List Value_type)) -> (Option (List Value_type)) ->
                 (Store_record Sort) -> Frame -> Sort -> Store_typing ->
                 Be_typing -> Sum ()
                 (SigT (Store_record Sort)
                 (SigT Frame
                 (SigT (List Administrative_instruction) (SigT Sort Reduce))))
t_progress_be host_function1 host_instance1 c bes ts1 ts2 vcs lab ret0 s f hs x x0 =
  let {tf = Tf ts1 ts2} in
  ssr_have __ (\_ hType ->
    ssr_have __ (\_ hType0 ->
      let {
       upd_label0 = upd_label
                      (upd_local_return c (map0 typeof (f_locs f)) ret0) lab}
      in
      ssr_have __ (\_ hType1 ->
        be_typing_rect (\c0 v lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_const v) Nil) (\ts3 ts4 _ ->
              eq_rect Nil (\_ ->
                eq_rect (Cons (typeof v) Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inl __) Nil) ts3) ts4 __) bes0)
            c0) (\c0 t op0 _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_unop t op0) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect (Cons t Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect_r
                             (upd_label
                               (upd_local_return c1 (map0 typeof (f_locs f0))
                                 ret1) lab0) (\_ ->
                             eq_rect (Cons (BI_unop t op0) Nil) (\_ _ _ ->
                               eq_rect (Cons t Nil) (\_ ->
                                 eq_rect (Cons t Nil) (\_ ->
                                   eq_rect (typeof v) (\_ _ _ _ _ _ _ ->
                                     case v of {
                                      VAL_int32 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (app_unop op0 (VAL_int32 s0)))) Nil)
                                       (ExistT hs (R_simple (Cons (AI_basic
                                       (BI_const (VAL_int32 s0))) (Cons
                                       (AI_basic (BI_unop T_i32 op0)) Nil))
                                       (Cons (AI_basic (BI_const
                                       (app_unop op0 (VAL_int32 s0)))) Nil) s
                                       f0 hs (Rs_unop (VAL_int32 s0) op0
                                       T_i32)))));
                                      VAL_int64 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (app_unop op0 (VAL_int64 s0)))) Nil)
                                       (ExistT hs (R_simple (Cons (AI_basic
                                       (BI_const (VAL_int64 s0))) (Cons
                                       (AI_basic (BI_unop T_i64 op0)) Nil))
                                       (Cons (AI_basic (BI_const
                                       (app_unop op0 (VAL_int64 s0)))) Nil) s
                                       f0 hs (Rs_unop (VAL_int64 s0) op0
                                       T_i64)))));
                                      VAL_float32 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (app_unop op0 (VAL_float32 s0)))) Nil)
                                       (ExistT hs (R_simple (Cons (AI_basic
                                       (BI_const (VAL_float32 s0))) (Cons
                                       (AI_basic (BI_unop T_f32 op0)) Nil))
                                       (Cons (AI_basic (BI_const
                                       (app_unop op0 (VAL_float32 s0)))) Nil)
                                       s f0 hs (Rs_unop (VAL_float32 s0) op0
                                       T_f32)))));
                                      VAL_float64 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (app_unop op0 (VAL_float64 s0)))) Nil)
                                       (ExistT hs (R_simple (Cons (AI_basic
                                       (BI_const (VAL_float64 s0))) (Cons
                                       (AI_basic (BI_unop T_f64 op0)) Nil))
                                       (Cons (AI_basic (BI_const
                                       (app_unop op0 (VAL_float64 s0)))) Nil)
                                       s f0 hs (Rs_unop (VAL_float64 s0) op0
                                       T_f64)))))}) t __ __ __ __ __ __ __)
                                   ts3 __) ts4 __) bes0 __ __ __) c0 __) t;
                        Cons _ _ -> false_rect}})) (Cons t Nil)) ts3) ts4 __)
              bes0) c0) (\c0 t op0 _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_binop t op0) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t (Cons t Nil)) (\_ ->
                eq_rect (Cons t Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil -> false_rect;
                        Cons v0 vcs2 ->
                         case vcs2 of {
                          Nil ->
                           eq_rect (typeof v) (\_ ->
                             eq_rect (typeof v0)
                               (eq_rect_r
                                 (upd_label
                                   (upd_local_return c1
                                     (map0 typeof (f_locs f0)) ret1) lab0)
                                 (\_ ->
                                 eq_rect (Cons (BI_binop t op0) Nil)
                                   (\_ _ _ ->
                                   eq_rect (Cons t (Cons t Nil)) (\_ ->
                                     eq_rect (Cons t Nil) (\_ ->
                                       eq_rect (typeof v) (\_ _ _ _ _ _ _ ->
                                         let {o = app_binop op0 v v0} in
                                         case o of {
                                          Some v1 -> ExistT s (ExistT f0
                                           (ExistT (Cons (AI_basic (BI_const
                                           v1)) Nil) (ExistT hs (R_simple
                                           (Cons (AI_basic (BI_const v))
                                           (Cons (AI_basic (BI_const v0))
                                           (Cons (AI_basic (BI_binop
                                           (typeof v0) op0)) Nil))) (Cons
                                           (AI_basic (BI_const v1)) Nil) s f0
                                           hs (Rs_binop_success v v0 v1 op0
                                           (typeof v0))))));
                                          None -> ExistT s (ExistT f0 (ExistT
                                           (Cons AI_trap Nil) (ExistT hs
                                           (R_simple (Cons (AI_basic
                                           (BI_const v)) (Cons (AI_basic
                                           (BI_const v0)) (Cons (AI_basic
                                           (BI_binop (typeof v0) op0)) Nil)))
                                           (Cons AI_trap Nil) s f0 hs
                                           (Rs_binop_failure v v0 op0
                                           (typeof v0))))))}) t __ __ __ __
                                         __ __ __) ts3 __) ts4 __) bes0 __ __
                                   __) c0 __) (typeof v)) t __;
                          Cons _ _ -> false_rect}}})) (Cons t (Cons t Nil)))
                  ts3) ts4 __) bes0) c0) (\c0 t _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_testop t) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect (Cons T_i32 Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect_r
                             (upd_label
                               (upd_local_return c1 (map0 typeof (f_locs f0))
                                 ret1) lab0) (\_ ->
                             eq_rect (Cons (BI_testop t) Nil) (\_ _ _ ->
                               eq_rect (Cons t Nil) (\_ ->
                                 eq_rect (Cons T_i32 Nil) (\_ ->
                                   eq_rect (typeof v) (\_ _ _ _ _ _ _ ->
                                     case v of {
                                      VAL_int32 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (VAL_int32
                                       (wasm_bool (app_testop_i i32t s0)))))
                                       Nil) (ExistT hs (R_simple (Cons
                                       (AI_basic (BI_const (VAL_int32 s0)))
                                       (Cons (AI_basic (BI_testop T_i32))
                                       Nil)) (Cons (AI_basic (BI_const
                                       (VAL_int32
                                       (wasm_bool (app_testop_i i32t s0)))))
                                       Nil) s f0 hs (Rs_testop_i32 s0)))));
                                      VAL_int64 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (VAL_int32
                                       (wasm_bool (app_testop_i i64t s0)))))
                                       Nil) (ExistT hs (R_simple (Cons
                                       (AI_basic (BI_const (VAL_int64 s0)))
                                       (Cons (AI_basic (BI_testop T_i64))
                                       Nil)) (Cons (AI_basic (BI_const
                                       (VAL_int32
                                       (wasm_bool (app_testop_i i64t s0)))))
                                       Nil) s f0 hs (Rs_testop_i64 s0)))));
                                      _ -> false_rect}) t __ __ __ __ __ __
                                     __) ts3 __) ts4 __) bes0 __ __ __) c0
                             __) t;
                        Cons _ _ -> false_rect}})) (Cons t Nil)) ts3) ts4 __)
              bes0) c0) (\c0 t op0 _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_relop t op0) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t (Cons t Nil)) (\_ ->
                eq_rect (Cons T_i32 Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil -> false_rect;
                        Cons v0 vcs2 ->
                         case vcs2 of {
                          Nil ->
                           eq_rect (typeof v) (\_ ->
                             eq_rect (typeof v0)
                               (eq_rect_r
                                 (upd_label
                                   (upd_local_return c1
                                     (map0 typeof (f_locs f0)) ret1) lab0)
                                 (\_ ->
                                 eq_rect (Cons (BI_relop t op0) Nil)
                                   (\_ _ _ ->
                                   eq_rect (Cons t (Cons t Nil)) (\_ ->
                                     eq_rect (Cons T_i32 Nil) (\_ ->
                                       eq_rect (typeof v) (\_ _ _ _ _ _ _ ->
                                         case v of {
                                          VAL_int32 s0 ->
                                           case v0 of {
                                            VAL_int32 s1 -> ExistT s (ExistT
                                             f0 (ExistT (Cons (AI_basic
                                             (BI_const (VAL_int32
                                             (wasm_bool
                                               (app_relop op0 (VAL_int32 s0)
                                                 (VAL_int32 s1)))))) Nil)
                                             (ExistT hs (R_simple (Cons
                                             (AI_basic (BI_const (VAL_int32
                                             s0))) (Cons (AI_basic (BI_const
                                             (VAL_int32 s1))) (Cons (AI_basic
                                             (BI_relop T_i32 op0)) Nil)))
                                             (Cons (AI_basic (BI_const
                                             (VAL_int32
                                             (wasm_bool
                                               (app_relop op0 (VAL_int32 s0)
                                                 (VAL_int32 s1)))))) Nil) s
                                             f0 hs (Rs_relop (VAL_int32 s0)
                                             (VAL_int32 s1) T_i32 op0)))));
                                            _ -> false_rect};
                                          VAL_int64 s0 ->
                                           case v0 of {
                                            VAL_int64 s1 -> ExistT s (ExistT
                                             f0 (ExistT (Cons (AI_basic
                                             (BI_const (VAL_int32
                                             (wasm_bool
                                               (app_relop op0 (VAL_int64 s0)
                                                 (VAL_int64 s1)))))) Nil)
                                             (ExistT hs (R_simple (Cons
                                             (AI_basic (BI_const (VAL_int64
                                             s0))) (Cons (AI_basic (BI_const
                                             (VAL_int64 s1))) (Cons (AI_basic
                                             (BI_relop T_i64 op0)) Nil)))
                                             (Cons (AI_basic (BI_const
                                             (VAL_int32
                                             (wasm_bool
                                               (app_relop op0 (VAL_int64 s0)
                                                 (VAL_int64 s1)))))) Nil) s
                                             f0 hs (Rs_relop (VAL_int64 s0)
                                             (VAL_int64 s1) T_i64 op0)))));
                                            _ -> false_rect};
                                          VAL_float32 s0 ->
                                           case v0 of {
                                            VAL_float32 s1 -> ExistT s
                                             (ExistT f0 (ExistT (Cons
                                             (AI_basic (BI_const (VAL_int32
                                             (wasm_bool
                                               (app_relop op0 (VAL_float32
                                                 s0) (VAL_float32 s1))))))
                                             Nil) (ExistT hs (R_simple (Cons
                                             (AI_basic (BI_const (VAL_float32
                                             s0))) (Cons (AI_basic (BI_const
                                             (VAL_float32 s1))) (Cons
                                             (AI_basic (BI_relop T_f32 op0))
                                             Nil))) (Cons (AI_basic (BI_const
                                             (VAL_int32
                                             (wasm_bool
                                               (app_relop op0 (VAL_float32
                                                 s0) (VAL_float32 s1))))))
                                             Nil) s f0 hs (Rs_relop
                                             (VAL_float32 s0) (VAL_float32
                                             s1) T_f32 op0)))));
                                            _ -> false_rect};
                                          VAL_float64 s0 ->
                                           case v0 of {
                                            VAL_float64 s1 -> ExistT s
                                             (ExistT f0 (ExistT (Cons
                                             (AI_basic (BI_const (VAL_int32
                                             (wasm_bool
                                               (app_relop op0 (VAL_float64
                                                 s0) (VAL_float64 s1))))))
                                             Nil) (ExistT hs (R_simple (Cons
                                             (AI_basic (BI_const (VAL_float64
                                             s0))) (Cons (AI_basic (BI_const
                                             (VAL_float64 s1))) (Cons
                                             (AI_basic (BI_relop T_f64 op0))
                                             Nil))) (Cons (AI_basic (BI_const
                                             (VAL_int32
                                             (wasm_bool
                                               (app_relop op0 (VAL_float64
                                                 s0) (VAL_float64 s1))))))
                                             Nil) s f0 hs (Rs_relop
                                             (VAL_float64 s0) (VAL_float64
                                             s1) T_f64 op0)))));
                                            _ -> false_rect}}) t __ __ __ __
                                         __ __ __) ts3 __) ts4 __) bes0 __ __
                                   __) c0 __) (typeof v)) t __;
                          Cons _ _ -> false_rect}}})) (Cons t (Cons t Nil)))
                  ts3) ts4 __) bes0) c0)
          (\c0 t1 t2 sx _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_cvtop t1 CVO_convert t2 sx) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t2 Nil) (\_ ->
                eq_rect (Cons t1 Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect_r
                             (upd_label
                               (upd_local_return c1 (map0 typeof (f_locs f0))
                                 ret1) lab0) (\_ ->
                             eq_rect (Cons (BI_cvtop t1 CVO_convert t2 sx)
                               Nil) (\_ _ _ ->
                               eq_rect (Cons t2 Nil) (\_ ->
                                 eq_rect (Cons t1 Nil) (\_ ->
                                   eq_rect (typeof v) (\_ _ _ _ _ _ _ _ ->
                                     let {o = cvt t1 sx v} in
                                     case o of {
                                      Some v0 ->
                                       case v of {
                                        VAL_int32 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons (AI_basic (BI_const
                                         v0)) Nil) (ExistT hs (R_simple (Cons
                                         (AI_basic (BI_const (VAL_int32 s0)))
                                         (Cons (AI_basic (BI_cvtop t1
                                         CVO_convert T_i32 sx)) Nil)) (Cons
                                         (AI_basic (BI_const v0)) Nil) s f0
                                         hs (Rs_convert_success T_i32 t1
                                         (VAL_int32 s0) v0 sx)))));
                                        VAL_int64 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons (AI_basic (BI_const
                                         v0)) Nil) (ExistT hs (R_simple (Cons
                                         (AI_basic (BI_const (VAL_int64 s0)))
                                         (Cons (AI_basic (BI_cvtop t1
                                         CVO_convert T_i64 sx)) Nil)) (Cons
                                         (AI_basic (BI_const v0)) Nil) s f0
                                         hs (Rs_convert_success T_i64 t1
                                         (VAL_int64 s0) v0 sx)))));
                                        VAL_float32 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons (AI_basic (BI_const
                                         v0)) Nil) (ExistT hs (R_simple (Cons
                                         (AI_basic (BI_const (VAL_float32
                                         s0))) (Cons (AI_basic (BI_cvtop t1
                                         CVO_convert T_f32 sx)) Nil)) (Cons
                                         (AI_basic (BI_const v0)) Nil) s f0
                                         hs (Rs_convert_success T_f32 t1
                                         (VAL_float32 s0) v0 sx)))));
                                        VAL_float64 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons (AI_basic (BI_const
                                         v0)) Nil) (ExistT hs (R_simple (Cons
                                         (AI_basic (BI_const (VAL_float64
                                         s0))) (Cons (AI_basic (BI_cvtop t1
                                         CVO_convert T_f64 sx)) Nil)) (Cons
                                         (AI_basic (BI_const v0)) Nil) s f0
                                         hs (Rs_convert_success T_f64 t1
                                         (VAL_float64 s0) v0 sx)))))};
                                      None ->
                                       case v of {
                                        VAL_int32 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons AI_trap Nil) (ExistT
                                         hs (R_simple (Cons (AI_basic
                                         (BI_const (VAL_int32 s0))) (Cons
                                         (AI_basic (BI_cvtop t1 CVO_convert
                                         T_i32 sx)) Nil)) (Cons AI_trap Nil)
                                         s f0 hs (Rs_convert_failure T_i32 t1
                                         (VAL_int32 s0) sx)))));
                                        VAL_int64 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons AI_trap Nil) (ExistT
                                         hs (R_simple (Cons (AI_basic
                                         (BI_const (VAL_int64 s0))) (Cons
                                         (AI_basic (BI_cvtop t1 CVO_convert
                                         T_i64 sx)) Nil)) (Cons AI_trap Nil)
                                         s f0 hs (Rs_convert_failure T_i64 t1
                                         (VAL_int64 s0) sx)))));
                                        VAL_float32 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons AI_trap Nil) (ExistT
                                         hs (R_simple (Cons (AI_basic
                                         (BI_const (VAL_float32 s0))) (Cons
                                         (AI_basic (BI_cvtop t1 CVO_convert
                                         T_f32 sx)) Nil)) (Cons AI_trap Nil)
                                         s f0 hs (Rs_convert_failure T_f32 t1
                                         (VAL_float32 s0) sx)))));
                                        VAL_float64 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons AI_trap Nil) (ExistT
                                         hs (R_simple (Cons (AI_basic
                                         (BI_const (VAL_float64 s0))) (Cons
                                         (AI_basic (BI_cvtop t1 CVO_convert
                                         T_f64 sx)) Nil)) (Cons AI_trap Nil)
                                         s f0 hs (Rs_convert_failure T_f64 t1
                                         (VAL_float64 s0) sx)))))}}) t2 __ __
                                     __ __ __ __ __ __) ts3 __) ts4 __) bes0
                               __ __ __) c0 __) t2;
                        Cons _ _ -> false_rect}})) (Cons t2 Nil)) ts3) ts4 __)
              bes0) c0) (\c0 t1 t2 _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_cvtop t1 CVO_reinterpret t2 None) Nil)
              (\ts3 ts4 _ ->
              eq_rect (Cons t2 Nil) (\_ ->
                eq_rect (Cons t1 Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect_r
                             (upd_label
                               (upd_local_return c1 (map0 typeof (f_locs f0))
                                 ret1) lab0) (\_ ->
                             eq_rect (Cons (BI_cvtop t1 CVO_reinterpret t2
                               None) Nil) (\_ _ _ ->
                               eq_rect (Cons t2 Nil) (\_ ->
                                 eq_rect (Cons t1 Nil) (\_ ->
                                   eq_rect (typeof v) (\_ _ _ _ _ _ _ _ ->
                                     case v of {
                                      VAL_int32 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (wasm_deserialise
                                         (bits (VAL_int32 s0)) t1))) Nil)
                                       (ExistT hs (R_simple (Cons (AI_basic
                                       (BI_const (VAL_int32 s0))) (Cons
                                       (AI_basic (BI_cvtop t1 CVO_reinterpret
                                       T_i32 None)) Nil)) (Cons (AI_basic
                                       (BI_const
                                       (wasm_deserialise
                                         (bits (VAL_int32 s0)) t1))) Nil) s
                                       f0 hs (Rs_reinterpret T_i32 t1
                                       (VAL_int32 s0))))));
                                      VAL_int64 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (wasm_deserialise
                                         (bits (VAL_int64 s0)) t1))) Nil)
                                       (ExistT hs (R_simple (Cons (AI_basic
                                       (BI_const (VAL_int64 s0))) (Cons
                                       (AI_basic (BI_cvtop t1 CVO_reinterpret
                                       T_i64 None)) Nil)) (Cons (AI_basic
                                       (BI_const
                                       (wasm_deserialise
                                         (bits (VAL_int64 s0)) t1))) Nil) s
                                       f0 hs (Rs_reinterpret T_i64 t1
                                       (VAL_int64 s0))))));
                                      VAL_float32 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (wasm_deserialise
                                         (bits (VAL_float32 s0)) t1))) Nil)
                                       (ExistT hs (R_simple (Cons (AI_basic
                                       (BI_const (VAL_float32 s0))) (Cons
                                       (AI_basic (BI_cvtop t1 CVO_reinterpret
                                       T_f32 None)) Nil)) (Cons (AI_basic
                                       (BI_const
                                       (wasm_deserialise
                                         (bits (VAL_float32 s0)) t1))) Nil) s
                                       f0 hs (Rs_reinterpret T_f32 t1
                                       (VAL_float32 s0))))));
                                      VAL_float64 s0 -> ExistT s (ExistT f0
                                       (ExistT (Cons (AI_basic (BI_const
                                       (wasm_deserialise
                                         (bits (VAL_float64 s0)) t1))) Nil)
                                       (ExistT hs (R_simple (Cons (AI_basic
                                       (BI_const (VAL_float64 s0))) (Cons
                                       (AI_basic (BI_cvtop t1 CVO_reinterpret
                                       T_f64 None)) Nil)) (Cons (AI_basic
                                       (BI_const
                                       (wasm_deserialise
                                         (bits (VAL_float64 s0)) t1))) Nil) s
                                       f0 hs (Rs_reinterpret T_f64 t1
                                       (VAL_float64 s0))))))}) t2 __ __ __ __
                                     __ __ __ __) ts3 __) ts4 __) bes0 __ __
                               __) c0 __) t2;
                        Cons _ _ -> false_rect}})) (Cons t2 Nil)) ts3) ts4 __)
              bes0) c0) (\c0 ts ts' lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons BI_unreachable Nil) (\ts3 ts4 _ ->
              eq_rect_r ts4 (\_ ->
                eq_rect_r ts3 (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr (ExistT s (ExistT f0
                    (ExistT (cat (v_to_e_list vcs0) (Cons AI_trap Nil))
                    (ExistT hs
                    (reduce_composition_left host_function1 host_instance1 s
                      (v_to_e_list vcs0) f0
                      (to_e_list (Cons BI_unreachable Nil)) s f0 (Cons
                      AI_trap Nil) hs hs (R_simple
                      (to_e_list (Cons BI_unreachable Nil)) (Cons AI_trap
                      Nil) s f0 hs Rs_unreachable))))))) ts4) ts') ts __)
              bes0) c0) (\c0 lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons BI_nop Nil) (\ts3 ts4 _ ->
              eq_rect Nil (\_ ->
                eq_rect Nil (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr (ExistT s (ExistT f0
                    (ExistT (cat (v_to_e_list vcs0) Nil) (ExistT hs
                    (reduce_composition_left host_function1 host_instance1 s
                      (v_to_e_list vcs0) f0 (to_e_list (Cons BI_nop Nil)) s
                      f0 Nil hs hs (R_simple (to_e_list (Cons BI_nop Nil))
                      Nil s f0 hs Rs_nop))))))) Nil) ts3) ts4 __) bes0) c0)
          (\c0 t lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons BI_drop Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect Nil (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect_r
                             (upd_label
                               (upd_local_return c1 (map0 typeof (f_locs f0))
                                 ret1) lab0) (\_ ->
                             eq_rect (Cons BI_drop Nil) (\_ _ _ ->
                               eq_rect (Cons t Nil) (\_ ->
                                 eq_rect Nil (\_ ->
                                   eq_rect (typeof v) (\_ _ _ -> ExistT s
                                     (ExistT f0 (ExistT Nil (ExistT hs
                                     (R_simple (Cons (AI_basic (BI_const v))
                                     (Cons (AI_basic BI_drop) Nil)) Nil s f0
                                     hs (Rs_drop v)))))) t __ __ __) ts3 __)
                                 ts4 __) bes0 __ __ __) c0 __) t;
                        Cons _ _ -> false_rect}})) (Cons t Nil)) ts3) ts4 __)
              bes0) c0) (\c0 t lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons BI_select Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t (Cons t (Cons T_i32 Nil))) (\_ ->
                eq_rect (Cons t Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil -> false_rect;
                        Cons v0 vcs2 ->
                         case vcs2 of {
                          Nil -> false_rect;
                          Cons v1 vcs3 ->
                           case vcs3 of {
                            Nil ->
                             eq_rect (typeof v) (\_ ->
                               eq_rect (typeof v0) (\_ ->
                                 eq_rect (typeof v1)
                                   (eq_rect_r
                                     (upd_label
                                       (upd_local_return c1
                                         (map0 typeof (f_locs f0)) ret1)
                                       lab0) (\_ ->
                                     eq_rect (Cons BI_select Nil) (\_ _ _ ->
                                       eq_rect (Cons t (Cons t (Cons T_i32
                                         Nil))) (\_ ->
                                         eq_rect (Cons t Nil) (\_ ->
                                           eq_rect (typeof v) (\_ _ _ ->
                                             case v1 of {
                                              VAL_int32 s0 ->
                                               let {
                                                b = eq_op i32 s0
                                                      (int_zero i32m)}
                                               in
                                               case b of {
                                                True -> ExistT s (ExistT f0
                                                 (ExistT (Cons (AI_basic
                                                 (BI_const v0)) Nil) (ExistT
                                                 hs (R_simple (Cons (AI_basic
                                                 (BI_const v)) (Cons
                                                 (AI_basic (BI_const v0))
                                                 (Cons (AI_basic (BI_const
                                                 (VAL_int32 s0))) (Cons
                                                 (AI_basic BI_select) Nil))))
                                                 (Cons (AI_basic (BI_const
                                                 v0)) Nil) s f0 hs
                                                 (Rs_select_false s0 v
                                                 v0)))));
                                                False -> ExistT s (ExistT f0
                                                 (ExistT (Cons (AI_basic
                                                 (BI_const v)) Nil) (ExistT
                                                 hs (R_simple (Cons (AI_basic
                                                 (BI_const v)) (Cons
                                                 (AI_basic (BI_const v0))
                                                 (Cons (AI_basic (BI_const
                                                 (VAL_int32 s0))) (Cons
                                                 (AI_basic BI_select) Nil))))
                                                 (Cons (AI_basic (BI_const
                                                 v)) Nil) s f0 hs
                                                 (Rs_select_true s0 v v0)))))};
                                              _ -> false_rect}) t __ __ __)
                                           ts3 __) ts4 __) bes0 __ __ __) c0
                                     __) T_i32) (typeof v)) t __ __;
                            Cons _ _ -> false_rect}}}})) (Cons t (Cons t
                    (Cons T_i32 Nil)))) ts3) ts4 __) bes0) c0)
          (\c0 tn tm es ->
          let {tf0 = Tf tn tm} in
          (\_ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_block tf0 es) Nil) (\ts3 ts4 _ ->
              eq_rect_r ts4 (\_ ->
                eq_rect_r ts3 (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr (ExistT s (ExistT f0
                    (ExistT (Cons (AI_label (length tm) Nil
                    (cat (v_to_e_list vcs0) (to_e_list es))) Nil) (ExistT hs
                    (R_simple
                    (cat (v_to_e_list vcs0)
                      (to_e_list (Cons (BI_block tf0 es) Nil))) (Cons
                    (AI_label (length tm) Nil
                    (cat (v_to_e_list vcs0) (to_e_list es))) Nil) s f0 hs
                    (Rs_block (v_to_e_list vcs0) es
                    (length (v_to_e_list vcs0)) (length tm) tn tm))))))) ts4)
                  tm) tn __) bes0) c0))
          (\c0 tn tm es _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_loop (Tf tn tm) es) Nil) (\ts3 ts4 _ ->
              eq_rect_r ts4 (\_ ->
                eq_rect_r ts3 (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr (ExistT s (ExistT f0
                    (ExistT (Cons (AI_label (length vcs0) (Cons (AI_basic
                    (BI_loop (Tf ts4 ts3) es)) Nil)
                    (cat (v_to_e_list vcs0) (to_e_list es))) Nil) (ExistT hs
                    (R_simple
                    (cat (v_to_e_list vcs0)
                      (to_e_list (Cons (BI_loop (Tf (map0 typeof vcs0) ts3)
                        es) Nil))) (Cons (AI_label (length vcs0) (Cons
                    (AI_basic (BI_loop (Tf ts4 ts3) es)) Nil)
                    (cat (v_to_e_list vcs0) (to_e_list es))) Nil) s f0 hs
                    (let {
                      _evar_0_ = Rs_loop (v_to_e_list vcs0) es (length vcs0)
                       (length ts3) ts4 ts3}
                     in
                     eq_rect_r ts4 _evar_0_ (map0 typeof vcs0)))))))) ts4) tm)
                tn __) bes0) c0)
          (\c0 tn tm es1 es2 _ _ _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_if (Tf tn tm) es1 es2) Nil) (\ts3 ts4 _ ->
              eq_rect (app tn (Cons T_i32 Nil)) (\_ ->
                eq_rect_r ts3 (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (let {hConstType = typeof_append tn T_i32 vcs0} in
                     case hConstType of {
                      ExistT v _ ->
                       let {
                        _evar_0_ = let {
                                    _evar_0_ = let {
                                                _evar_0_ = case v of {
                                                            VAL_int32 s0 ->
                                                             let {
                                                              b = eq_op i32
                                                                    s0
                                                                    (int_zero
                                                                    i32m)}
                                                             in
                                                             case b of {
                                                              True -> ExistT
                                                               s (ExistT f0
                                                               (ExistT
                                                               (cat
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    tn) vcs0))
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_block
                                                                 (Tf tn ts3)
                                                                 es2)) Nil))
                                                               (ExistT hs
                                                               (reduce_composition_left
                                                                 host_function1
                                                                 host_instance1
                                                                 s
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    tn) vcs0))
                                                                 f0 (Cons
                                                                 (AI_basic
                                                                 (BI_const
                                                                 (VAL_int32
                                                                 s0))) (Cons
                                                                 (AI_basic
                                                                 (BI_if (Tf
                                                                 tn ts3) es1
                                                                 es2)) Nil))
                                                                 s f0 (Cons
                                                                 (AI_basic
                                                                 (BI_block
                                                                 (Tf tn ts3)
                                                                 es2)) Nil)
                                                                 hs hs
                                                                 (R_simple
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_const
                                                                 (VAL_int32
                                                                 s0))) (Cons
                                                                 (AI_basic
                                                                 (BI_if (Tf
                                                                 tn ts3) es1
                                                                 es2)) Nil))
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_block
                                                                 (Tf tn ts3)
                                                                 es2)) Nil) s
                                                                 f0 hs
                                                                 (Rs_if_false
                                                                 s0 (Tf tn
                                                                 ts3) es1
                                                                 es2))))));
                                                              False -> ExistT
                                                               s (ExistT f0
                                                               (ExistT
                                                               (cat
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    tn) vcs0))
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_block
                                                                 (Tf tn ts3)
                                                                 es1)) Nil))
                                                               (ExistT hs
                                                               (reduce_composition_left
                                                                 host_function1
                                                                 host_instance1
                                                                 s
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    tn) vcs0))
                                                                 f0 (Cons
                                                                 (AI_basic
                                                                 (BI_const
                                                                 (VAL_int32
                                                                 s0))) (Cons
                                                                 (AI_basic
                                                                 (BI_if (Tf
                                                                 tn ts3) es1
                                                                 es2)) Nil))
                                                                 s f0 (Cons
                                                                 (AI_basic
                                                                 (BI_block
                                                                 (Tf tn ts3)
                                                                 es1)) Nil)
                                                                 hs hs
                                                                 (R_simple
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_const
                                                                 (VAL_int32
                                                                 s0))) (Cons
                                                                 (AI_basic
                                                                 (BI_if (Tf
                                                                 tn ts3) es1
                                                                 es2)) Nil))
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_block
                                                                 (Tf tn ts3)
                                                                 es1)) Nil) s
                                                                 f0 hs
                                                                 (Rs_if_true
                                                                 s0 (Tf tn
                                                                 ts3) es1
                                                                 es2))))))};
                                                            _ -> false_rect}}
                                               in
                                               eq_rect
                                                 (cat
                                                   (v_to_e_list
                                                     (take (size0 tn) vcs0))
                                                   (cat
                                                     (v_to_e_list (Cons v
                                                       Nil))
                                                     (to_e_list (Cons (BI_if
                                                       (Tf tn ts3) es1 es2)
                                                       Nil)))) _evar_0_
                                                 (cat
                                                   (cat
                                                     (v_to_e_list
                                                       (take (size0 tn) vcs0))
                                                     (v_to_e_list (Cons v
                                                       Nil)))
                                                   (to_e_list (Cons (BI_if
                                                     (Tf tn ts3) es1 es2)
                                                     Nil)))}
                                   in
                                   eq_rect
                                     (cat
                                       (v_to_e_list (take (size0 tn) vcs0))
                                       (v_to_e_list (Cons v Nil))) _evar_0_
                                     (v_to_e_list
                                       (cat (take (size0 tn) vcs0) (Cons v
                                         Nil)))}
                       in
                       eq_rect_r (cat (take (size0 tn) vcs0) (Cons v Nil))
                         _evar_0_ vcs0})) (app tn (Cons T_i32 Nil))) tm) ts4
                __) bes0) c0) (\c0 i t1s ts t2s _ _ lab0 ret1 f0 c1 _ _ ->
          let {
           x1 = \_ ->
            eq_rect_r
              (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
                lab0) (\bes0 _ _ _ ->
              eq_rect (Cons (BI_br i) Nil) (\ts3 ts4 _ ->
                eq_rect (app t1s (unsafeCoerce ts)) (\_ ->
                  eq_rect_r ts3 (\vcs0 _ ->
                    eq_rect (map0 (unsafeCoerce typeof) vcs0)
                      (eq_rect_r
                        (upd_label
                          (upd_local_return c1 (map0 typeof (f_locs f0))
                            ret1) lab0) (\_ _ _ ->
                        eq_rect (Cons (BI_br i) Nil) (\_ _ _ ->
                          eq_rect (app t1s (unsafeCoerce ts)) (\_ ->
                            eq_rect_r ts3 (\_ -> false_rect) t2s __) ts4 __)
                          bes0 __ __ __) c0 __ __ __)
                      (app t1s (unsafeCoerce ts))) t2s) ts4 __) bes0) c0}
          in
          unsafeCoerce x1 __) (\c0 i ts _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_br_if i) Nil) (\ts3 ts4 _ ->
              eq_rect (app (unsafeCoerce ts) (Cons T_i32 Nil)) (\_ ->
                eq_rect_r (unsafeCoerce ts3) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (let {hConstType = typeof_append ts3 T_i32 vcs0} in
                     case hConstType of {
                      ExistT v _ ->
                       let {
                        _evar_0_ = let {
                                    _evar_0_ = let {
                                                _evar_0_ = case v of {
                                                            VAL_int32 s0 ->
                                                             let {
                                                              b = eq_op i32
                                                                    s0
                                                                    (int_zero
                                                                    i32m)}
                                                             in
                                                             case b of {
                                                              True -> ExistT
                                                               s (ExistT f0
                                                               (ExistT
                                                               (cat
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    ts3)
                                                                    vcs0))
                                                                 Nil) (ExistT
                                                               hs
                                                               (reduce_composition_left
                                                                 host_function1
                                                                 host_instance1
                                                                 s
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    ts3)
                                                                    vcs0)) f0
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_const
                                                                 (VAL_int32
                                                                 s0))) (Cons
                                                                 (AI_basic
                                                                 (BI_br_if
                                                                 i)) Nil)) s
                                                                 f0 Nil hs hs
                                                                 (R_simple
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_const
                                                                 (VAL_int32
                                                                 s0))) (Cons
                                                                 (AI_basic
                                                                 (BI_br_if
                                                                 i)) Nil))
                                                                 Nil s f0 hs
                                                                 (Rs_br_if_false
                                                                 s0 i))))));
                                                              False -> ExistT
                                                               s (ExistT f0
                                                               (ExistT
                                                               (cat
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    ts3)
                                                                    vcs0))
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_br i))
                                                                 Nil))
                                                               (ExistT hs
                                                               (reduce_composition_left
                                                                 host_function1
                                                                 host_instance1
                                                                 s
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    ts3)
                                                                    vcs0)) f0
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_const
                                                                 (VAL_int32
                                                                 s0))) (Cons
                                                                 (AI_basic
                                                                 (BI_br_if
                                                                 i)) Nil)) s
                                                                 f0 (Cons
                                                                 (AI_basic
                                                                 (BI_br i))
                                                                 Nil) hs hs
                                                                 (R_simple
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_const
                                                                 (VAL_int32
                                                                 s0))) (Cons
                                                                 (AI_basic
                                                                 (BI_br_if
                                                                 i)) Nil))
                                                                 (Cons
                                                                 (AI_basic
                                                                 (BI_br i))
                                                                 Nil) s f0 hs
                                                                 (Rs_br_if_true
                                                                 s0 i))))))};
                                                            _ -> false_rect}}
                                               in
                                               eq_rect
                                                 (cat
                                                   (v_to_e_list
                                                     (take (size0 ts3) vcs0))
                                                   (cat
                                                     (v_to_e_list (Cons v
                                                       Nil))
                                                     (to_e_list (Cons
                                                       (BI_br_if i) Nil))))
                                                 _evar_0_
                                                 (cat
                                                   (cat
                                                     (v_to_e_list
                                                       (take (size0 ts3)
                                                         vcs0))
                                                     (v_to_e_list (Cons v
                                                       Nil)))
                                                   (to_e_list (Cons (BI_br_if
                                                     i) Nil)))}
                                   in
                                   eq_rect
                                     (cat
                                       (v_to_e_list (take (size0 ts3) vcs0))
                                       (v_to_e_list (Cons v Nil))) _evar_0_
                                     (v_to_e_list
                                       (cat (take (size0 ts3) vcs0) (Cons v
                                         Nil)))}
                       in
                       eq_rect_r (cat (take (size0 ts3) vcs0) (Cons v Nil))
                         _evar_0_ vcs0})) (app ts3 (Cons T_i32 Nil))) ts) ts4
                __) bes0) c0) (\c0 i ins ts t1s t2s _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_br_table ins i) Nil) (\ts3 ts4 _ ->
              eq_rect
                (app (unsafeCoerce t1s)
                  (app (unsafeCoerce ts) (Cons T_i32 Nil))) (\_ ->
                eq_rect_r ts3 (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (let {
                      _evar_0_ = let {
                                  _evar_0_ = \_ ->
                                   let {
                                    h5 = typeof_append (unsafeCoerce ts)
                                           T_i32 (drop (size0 t1s) vcs0)}
                                   in
                                   case h5 of {
                                    ExistT v _ ->
                                     case v of {
                                      VAL_int32 s0 ->
                                       let {
                                        _evar_0_ = let {
                                                    _evar_0_ = let {
                                                                _evar_0_ = 
                                                                 let {
                                                                  _evar_0_ = 
                                                                   let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    b = 
                                                                    leq (S
                                                                    (nat_of_uint
                                                                    i32m s0))
                                                                    (length
                                                                    ins)}
                                                                    in
                                                                    case b of {
                                                                     True ->
                                                                    let {
                                                                    o = 
                                                                    nth_error
                                                                    ins
                                                                    (nat_of_uint
                                                                    i32m s0)}
                                                                    in
                                                                    case o of {
                                                                     Some n ->
                                                                    ExistT s
                                                                    (ExistT
                                                                    f0
                                                                    (ExistT
                                                                    (cat
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br
                                                                    n)) Nil))
                                                                    (ExistT
                                                                    hs
                                                                    (reduce_composition_left
                                                                    host_function1
                                                                    host_instance1
                                                                    s
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))))
                                                                    f0 (Cons
                                                                    (AI_basic
                                                                    (BI_const
                                                                    (VAL_int32
                                                                    s0)))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil)) s
                                                                    f0 (Cons
                                                                    (AI_basic
                                                                    (BI_br
                                                                    n)) Nil)
                                                                    hs hs
                                                                    (R_simple
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_const
                                                                    (VAL_int32
                                                                    s0)))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br
                                                                    n)) Nil)
                                                                    s f0 hs
                                                                    (Rs_br_table
                                                                    ins s0 i
                                                                    n))))));
                                                                     None ->
                                                                    false_rect};
                                                                     False ->
                                                                    ExistT s
                                                                    (ExistT
                                                                    f0
                                                                    (ExistT
                                                                    (cat
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br
                                                                    i)) Nil))
                                                                    (ExistT
                                                                    hs
                                                                    (reduce_composition_left
                                                                    host_function1
                                                                    host_instance1
                                                                    s
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))))
                                                                    f0
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil)) s
                                                                    f0 (Cons
                                                                    (AI_basic
                                                                    (BI_br
                                                                    i)) Nil)
                                                                    hs hs
                                                                    (R_simple
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br
                                                                    i)) Nil)
                                                                    s f0 hs
                                                                    (Rs_br_table_length
                                                                    ins s0
                                                                    i))))))}}
                                                                    in
                                                                    eq_rect_r
                                                                    (cat
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))))
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil)))
                                                                    _evar_0_
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)))
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil))))}
                                                                   in
                                                                   eq_rect
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)))
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil)))
                                                                    _evar_0_
                                                                    (cat
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)))
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil)))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil))}
                                                                 in
                                                                 eq_rect
                                                                   (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (cat
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)))
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil)))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil)))
                                                                   _evar_0_
                                                                   (cat
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)))
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_br_table
                                                                    ins i))
                                                                    Nil))}
                                                               in
                                                               eq_rect
                                                                 (cat
                                                                   (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)))
                                                                   (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil)))
                                                                 _evar_0_
                                                                 (v_to_e_list
                                                                   (cat
                                                                    (take
                                                                    (size0
                                                                    (unsafeCoerce
                                                                    ts))
                                                                    (drop
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil)))}
                                                   in
                                                   eq_rect
                                                     (cat
                                                       (v_to_e_list
                                                         (take (size0 t1s)
                                                           vcs0))
                                                       (v_to_e_list
                                                         (cat
                                                           (take
                                                             (size0
                                                               (unsafeCoerce
                                                                 ts))
                                                             (drop
                                                               (size0 t1s)
                                                               vcs0)) (Cons
                                                           (VAL_int32 s0)
                                                           Nil)))) _evar_0_
                                                     (v_to_e_list
                                                       (cat
                                                         (take (size0 t1s)
                                                           vcs0)
                                                         (cat
                                                           (take
                                                             (size0
                                                               (unsafeCoerce
                                                                 ts))
                                                             (drop
                                                               (size0 t1s)
                                                               vcs0)) (Cons
                                                           (VAL_int32 s0)
                                                           Nil))))}
                                       in
                                       eq_rect_r
                                         (cat
                                           (take (size0 (unsafeCoerce ts))
                                             (drop (size0 t1s) vcs0)) (Cons
                                           (VAL_int32 s0) Nil)) _evar_0_
                                         (drop (size0 t1s) vcs0);
                                      _ -> false_rect}}}
                                 in
                                 eq_rect
                                   (map0 typeof (drop (size0 t1s) vcs0))
                                   _evar_0_
                                   (drop (size0 t1s) (map0 typeof vcs0)) __}
                     in
                     eq_rect_r
                       (cat (take (size0 t1s) vcs0) (drop (size0 t1s) vcs0))
                       _evar_0_ vcs0))
                    (app (unsafeCoerce t1s)
                      (app (unsafeCoerce ts) (Cons T_i32 Nil)))) t2s) ts4 __)
              bes0) c0) (\c0 ts t1s t2s _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons BI_return Nil) (\ts3 ts4 _ ->
              eq_rect (app t1s ts) (\_ ->
                eq_rect_r ts3 (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0)
                    (eq_rect_r
                      (upd_label
                        (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
                        lab0) (\_ _ ->
                      eq_rect (Cons BI_return Nil) (\_ _ _ ->
                        eq_rect (app t1s ts) (\_ ->
                          eq_rect_r ts3 (\_ -> false_rect) t2s __) ts4 __)
                        bes0 __ __ __) c0 __ __) (app t1s ts)) t2s) ts4 __)
              bes0) c0) (\c0 i tf0 _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_call i) Nil) (\ts3 ts4 _ ->
              eq_rect_r (Tf ts4 ts3) (\vcs0 _ ->
                eq_rect (map0 typeof vcs0) (Inr
                  (eq_rect_r
                    (upd_label
                      (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
                      lab0) (\_ _ _ ->
                    eq_rect (Cons (BI_call i) Nil) (\_ _ _ ->
                      eq_rect_r (Tf ts4 ts3) (\_ _ ->
                        eq_rect (map0 typeof vcs0) (\_ _ _ ->
                          let {
                           e = func_context_store host_function1 s
                                 (f_inst f0) c1 i (Tf (map0 typeof vcs0) ts3)}
                          in
                          case e of {
                           ExistT a _ -> ExistT s (ExistT f0 (ExistT
                            (cat (v_to_e_list vcs0) (Cons (AI_invoke a) Nil))
                            (ExistT hs
                            (reduce_composition_left host_function1
                              host_instance1 s (v_to_e_list vcs0) f0 (Cons
                              (AI_basic (BI_call i)) Nil) s f0 (Cons
                              (AI_invoke a) Nil) hs hs (R_call s f0 i a hs)))))})
                          ts4 __ __ __) tf0 __ __) bes0 __ __ __) c0 __ __
                    __)) ts4) tf0) bes0) c0)
          (\c0 i t1s t2s _ _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_call_indirect i) Nil) (\ts3 ts4 _ ->
              eq_rect (app t1s (Cons T_i32 Nil)) (\_ ->
                eq_rect_r ts3 (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (let {hConstType = typeof_append t1s T_i32 vcs0} in
                     case hConstType of {
                      ExistT v _ ->
                       case v of {
                        VAL_int32 s0 ->
                         let {
                          _evar_0_ = let {
                                      _evar_0_ = let {
                                                  _evar_0_ = eq_rect_r
                                                               (upd_label
                                                                 (upd_local_return
                                                                   c1
                                                                   (map0
                                                                    typeof
                                                                    (f_locs
                                                                    f0))
                                                                   ret1)
                                                                 lab0)
                                                               (\_ _ _ _ ->
                                                               eq_rect (Cons
                                                                 (BI_call_indirect
                                                                 i) Nil)
                                                                 (\_ _ _ ->
                                                                 eq_rect
                                                                   (app t1s
                                                                    (Cons
                                                                    T_i32
                                                                    Nil))
                                                                   (\_ ->
                                                                   eq_rect_r
                                                                    ts3
                                                                    (\_ _ ->
                                                                    ExistT s
                                                                    (ExistT
                                                                    f0
                                                                    (let {
                                                                    o = 
                                                                    stab_addr
                                                                    host_function1
                                                                    s f0
                                                                    (nat_of_uint
                                                                    i32m s0)}
                                                                    in
                                                                    case o of {
                                                                     Some a ->
                                                                    let {
                                                                    hstabaddr = 
                                                                    store_typing_stabaddr
                                                                    host_function1
                                                                    s f0 c1
                                                                    (nat_of_uint
                                                                    i32m s0)
                                                                    a x}
                                                                    in
                                                                    case hstabaddr of {
                                                                     ExistT cl
                                                                    _ ->
                                                                    let {
                                                                    b = 
                                                                    eq_op
                                                                    (option_eqType
                                                                    function_type_eqType)
                                                                    (unsafeCoerce
                                                                    stypes
                                                                    host_function1
                                                                    s
                                                                    (f_inst
                                                                    f0) i)
                                                                    (unsafeCoerce
                                                                    (Some
                                                                    (cl_type
                                                                    host_function1
                                                                    cl)))}
                                                                    in
                                                                    case b of {
                                                                     True ->
                                                                    ExistT
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (Cons
                                                                    (AI_invoke
                                                                    a) Nil))
                                                                    (ExistT
                                                                    hs
                                                                    (reduce_composition_left
                                                                    host_function1
                                                                    host_instance1
                                                                    s
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)) f0
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_call_indirect
                                                                    i)) Nil))
                                                                    s f0
                                                                    (Cons
                                                                    (AI_invoke
                                                                    a) Nil)
                                                                    hs hs
                                                                    (R_call_indirect_success
                                                                    s f0 i a
                                                                    cl s0
                                                                    hs)));
                                                                     False ->
                                                                    ExistT
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (Cons
                                                                    AI_trap
                                                                    Nil))
                                                                    (ExistT
                                                                    hs
                                                                    (reduce_composition_left
                                                                    host_function1
                                                                    host_instance1
                                                                    s
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)) f0
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_call_indirect
                                                                    i)) Nil))
                                                                    s f0
                                                                    (Cons
                                                                    AI_trap
                                                                    Nil) hs
                                                                    hs
                                                                    (R_call_indirect_failure1
                                                                    s f0 i a
                                                                    cl s0
                                                                    hs)))}};
                                                                     None ->
                                                                    ExistT
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0))
                                                                    (Cons
                                                                    AI_trap
                                                                    Nil))
                                                                    (ExistT
                                                                    hs
                                                                    (reduce_composition_left
                                                                    host_function1
                                                                    host_instance1
                                                                    s
                                                                    (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    t1s)
                                                                    vcs0)) f0
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons
                                                                    (VAL_int32
                                                                    s0) Nil))
                                                                    (Cons
                                                                    (AI_basic
                                                                    (BI_call_indirect
                                                                    i)) Nil))
                                                                    s f0
                                                                    (Cons
                                                                    AI_trap
                                                                    Nil) hs
                                                                    hs
                                                                    (R_call_indirect_failure2
                                                                    s f0 i s0
                                                                    hs)))})))
                                                                    t2s __ __)
                                                                   ts4 __)
                                                                 bes0 __ __
                                                                 __) c0 __ __
                                                               __ __}
                                                 in
                                                 eq_rect
                                                   (cat
                                                     (v_to_e_list
                                                       (take (size0 t1s)
                                                         vcs0))
                                                     (cat
                                                       (v_to_e_list (Cons
                                                         (VAL_int32 s0) Nil))
                                                       (Cons (AI_basic
                                                       (BI_call_indirect i))
                                                       Nil))) _evar_0_
                                                   (cat
                                                     (cat
                                                       (v_to_e_list
                                                         (take (size0 t1s)
                                                           vcs0))
                                                       (v_to_e_list (Cons
                                                         (VAL_int32 s0) Nil)))
                                                     (Cons (AI_basic
                                                     (BI_call_indirect i))
                                                     Nil))}
                                     in
                                     eq_rect
                                       (cat
                                         (v_to_e_list
                                           (take (size0 t1s) vcs0))
                                         (v_to_e_list (Cons (VAL_int32 s0)
                                           Nil))) _evar_0_
                                       (v_to_e_list
                                         (cat (take (size0 t1s) vcs0) (Cons
                                           (VAL_int32 s0) Nil)))}
                         in
                         eq_rect_r
                           (cat (take (size0 t1s) vcs0) (Cons (VAL_int32 s0)
                             Nil)) _evar_0_ vcs0;
                        _ -> false_rect}})) (app t1s (Cons T_i32 Nil))) t2s)
                ts4 __) bes0) c0) (\c0 i t _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_get_local i) Nil) (\ts3 ts4 _ ->
              eq_rect Nil (\_ ->
                eq_rect (Cons t Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil ->
                       eq_rect_r
                         (upd_label
                           (upd_local_return c1 (map0 typeof (f_locs f0))
                             ret1) lab0) (\_ _ _ ->
                         eq_rect (Cons (BI_get_local i) Nil) (\_ _ _ ->
                           eq_rect Nil (\_ ->
                             eq_rect (Cons t Nil) (\_ ->
                               let {e = nth_error_map (f_locs f0) i typeof t}
                               in
                               case e of {
                                ExistT x' _ ->
                                 let {
                                  _evar_0_ = \_ ->
                                   let {
                                    _evar_0_ = \_ -> ExistT s (ExistT f0
                                     (ExistT (Cons (AI_basic (BI_const x'))
                                     Nil) (ExistT hs (R_get_local f0 x' i s
                                     hs))))}
                                   in
                                   eq_rect_r (size0 (f_locs f0)) _evar_0_
                                     (size0 (map0 typeof (f_locs f0))) __}
                                 in
                                 eq_rect_r (size0 (map0 typeof (f_locs f0)))
                                   _evar_0_
                                   (length (map0 typeof (f_locs f0))) __})
                               ts3 __) ts4 __) bes0 __ __ __) c0 __ __ __;
                      Cons _ _ -> false_rect})) Nil) ts3) ts4 __) bes0) c0)
          (\c0 i t _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_set_local i) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect Nil (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect_r
                             (upd_label
                               (upd_local_return c1 (map0 typeof (f_locs f0))
                                 ret1) lab0) (\_ _ _ ->
                             eq_rect (Cons (BI_set_local i) Nil) (\_ _ _ ->
                               eq_rect (Cons t Nil) (\_ ->
                                 eq_rect Nil (\_ ->
                                   eq_rect (typeof v) (\_ _ _ _ ->
                                     let {
                                      _evar_0_ = \_ ->
                                       let {
                                        _evar_0_ = \_ ->
                                         let {
                                          _evar_0_ = \_ -> ExistT s (ExistT
                                           (Build_frame
                                           (set_nth v (f_locs f0) i v)
                                           (f_inst f0)) (ExistT Nil (ExistT
                                           hs (R_set_local f0 (Build_frame
                                           (set_nth v (f_locs f0) i v)
                                           (f_inst f0)) i v s v hs))))}
                                         in
                                         eq_rect (length (f_locs f0))
                                           _evar_0_ (size0 (f_locs f0)) __}
                                       in
                                       eq_rect_r (size0 (f_locs f0)) _evar_0_
                                         (size0 (map0 typeof (f_locs f0))) __}
                                     in
                                     eq_rect_r
                                       (size0 (map0 typeof (f_locs f0)))
                                       _evar_0_
                                       (length (map0 typeof (f_locs f0))) __)
                                     t __ __ __ __) ts3 __) ts4 __) bes0 __
                               __ __) c0 __ __ __) t;
                        Cons _ _ -> false_rect}})) (Cons t Nil)) ts3) ts4 __)
              bes0) c0) (\c0 i t _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_tee_local i) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect (Cons t Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect_r
                             (upd_label
                               (upd_local_return c1 (map0 typeof (f_locs f0))
                                 ret1) lab0) (\_ _ _ ->
                             eq_rect (Cons (BI_tee_local i) Nil) (\_ _ _ ->
                               eq_rect (Cons t Nil) (\_ ->
                                 eq_rect (Cons t Nil) (\_ ->
                                   eq_rect (typeof v) (\_ _ _ _ -> ExistT s
                                     (ExistT f0 (ExistT (Cons (AI_basic
                                     (BI_const v)) (Cons (AI_basic (BI_const
                                     v)) (Cons (AI_basic (BI_set_local i))
                                     Nil))) (ExistT hs (R_simple (Cons
                                     (AI_basic (BI_const v)) (Cons (AI_basic
                                     (BI_tee_local i)) Nil)) (Cons (AI_basic
                                     (BI_const v)) (Cons (AI_basic (BI_const
                                     v)) (Cons (AI_basic (BI_set_local i))
                                     Nil))) s f0 hs (Rs_tee_local i (AI_basic
                                     (BI_const v)))))))) t __ __ __ __) ts3
                                   __) ts4 __) bes0 __ __ __) c0 __ __ __) t;
                        Cons _ _ -> false_rect}})) (Cons t Nil)) ts3) ts4 __)
              bes0) c0) (\c0 i t _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_get_global i) Nil) (\ts3 ts4 _ ->
              eq_rect Nil (\_ ->
                eq_rect (Cons t Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil ->
                       eq_rect_r
                         (upd_label
                           (upd_local_return c1 (map0 typeof (f_locs f0))
                             ret1) lab0) (\_ _ _ ->
                         eq_rect (Cons (BI_get_global i) Nil) (\_ _ _ ->
                           eq_rect Nil (\_ ->
                             eq_rect (Cons t Nil) (\_ ->
                               let {o = nth_error (tc_global c1) i} in
                               case o of {
                                Some _ ->
                                 let {
                                  o0 = sglob_val host_function1 s (f_inst f0)
                                         i}
                                 in
                                 case o0 of {
                                  Some v -> ExistT s (ExistT f0 (ExistT (Cons
                                   (AI_basic (BI_const v)) Nil) (ExistT hs
                                   (R_get_global s f0 i v hs))));
                                  None -> false_rect};
                                None -> false_rect}) ts3 __) ts4 __) bes0 __
                           __ __) c0 __ __ __;
                      Cons _ _ -> false_rect})) Nil) ts3) ts4 __) bes0) c0)
          (\c0 i g t _ _ _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_set_global i) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons t Nil) (\_ ->
                eq_rect Nil (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect (tg_t g) (\_ _ _ _ _ ->
                             eq_rect_r
                               (upd_label
                                 (upd_local_return c1
                                   (map0 typeof (f_locs f0)) ret1) lab0)
                               (\_ _ _ ->
                               eq_rect (Cons (BI_set_global i) Nil)
                                 (\_ _ _ ->
                                 eq_rect (Cons (tg_t g) Nil) (\_ ->
                                   eq_rect Nil (\_ ->
                                     let {
                                      o = supdate_glob host_function1 s
                                            (f_inst f0) i v}
                                     in
                                     case o of {
                                      Some s0 -> ExistT s0 (ExistT f0 (ExistT
                                       Nil (ExistT hs (R_set_global s f0 i v
                                       s0 hs))));
                                      None -> false_rect}) ts3 __) ts4 __)
                                 bes0 __ __ __) c0 __ __ __) t __ __ __ __
                             __) t;
                        Cons _ _ -> false_rect}})) (Cons t Nil)) ts3) ts4 __)
              bes0) c0) (\c0 a off tp_sx t _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_load t tp_sx a off) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons T_i32 Nil) (\_ ->
                eq_rect (Cons t Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (eq_rect_r
                      (upd_label
                        (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
                        lab0) (\_ _ ->
                      eq_rect (Cons (BI_load t tp_sx a off) Nil) (\_ _ _ ->
                        eq_rect (Cons T_i32 Nil) (\_ ->
                          eq_rect (Cons t Nil) (\_ -> ExistT s (ExistT f0
                            (case vcs0 of {
                              Nil -> false_rect;
                              Cons v vcs1 ->
                               case vcs1 of {
                                Nil ->
                                 eq_rect (typeof v)
                                   (case v of {
                                     VAL_int32 s0 ->
                                      let {
                                       n = mem_context_store host_function1 s
                                             (f_inst f0) c1}
                                      in
                                      case n of {
                                       ExistT n0 _ ->
                                        let {o = nth_error (s_mems s) n0} in
                                        case o of {
                                         Some m ->
                                          case tp_sx of {
                                           Some p ->
                                            case p of {
                                             Pair tp sx ->
                                              let {
                                               o0 = load_packed sx m
                                                      (n_of_uint i32m s0) off
                                                      (tp_length tp)
                                                      (t_length t)}
                                              in
                                              case o0 of {
                                               Some b -> ExistT (Cons
                                                (AI_basic (BI_const
                                                (wasm_deserialise b t))) Nil)
                                                (ExistT hs
                                                (R_load_packed_success s n0
                                                f0 t tp s0 a off m b sx hs));
                                               None -> ExistT (Cons AI_trap
                                                Nil) (ExistT hs
                                                (R_load_packed_failure s n0
                                                f0 t tp s0 a off m sx hs))}};
                                           None ->
                                            let {
                                             o0 = load m (n_of_uint i32m s0)
                                                    off (t_length t)}
                                            in
                                            case o0 of {
                                             Some b -> ExistT (Cons (AI_basic
                                              (BI_const
                                              (wasm_deserialise b t))) Nil)
                                              (ExistT hs (R_load_success s n0
                                              f0 t b s0 a off m hs));
                                             None -> ExistT (Cons AI_trap
                                              Nil) (ExistT hs (R_load_failure
                                              s n0 f0 t s0 a off m hs))}};
                                         None -> false_rect}};
                                     _ -> false_rect}) T_i32;
                                Cons _ _ -> false_rect}}))) ts3 __) ts4 __)
                        bes0 __ __ __) c0 __ __)) (Cons T_i32 Nil)) ts3) ts4
                __) bes0) c0) (\c0 a off tp t _ _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons (BI_store t tp a off) Nil) (\ts3 ts4 _ ->
              eq_rect (Cons T_i32 (Cons t Nil)) (\_ ->
                eq_rect Nil (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (eq_rect_r
                      (upd_label
                        (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
                        lab0) (\_ _ ->
                      eq_rect (Cons (BI_store t tp a off) Nil) (\_ _ _ ->
                        eq_rect (Cons T_i32 (Cons t Nil)) (\_ ->
                          eq_rect Nil (\_ ->
                            case vcs0 of {
                             Nil -> false_rect;
                             Cons v vcs1 ->
                              case vcs1 of {
                               Nil -> false_rect;
                               Cons v0 vcs2 ->
                                case vcs2 of {
                                 Nil ->
                                  eq_rect (typeof v) (\_ ->
                                    eq_rect (typeof v0)
                                      (eq_rect (typeof v0) (\_ _ _ _ _ _ _ ->
                                        case v of {
                                         VAL_int32 s0 ->
                                          let {
                                           n = mem_context_store
                                                 host_function1 s (f_inst f0)
                                                 c1}
                                          in
                                          case n of {
                                           ExistT n0 _ ->
                                            let {o = nth_error (s_mems s) n0}
                                            in
                                            case o of {
                                             Some m ->
                                              case tp of {
                                               Some tp0 ->
                                                let {
                                                 o0 = store_packed m
                                                        (n_of_uint i32m s0)
                                                        off (bits v0)
                                                        (tp_length tp0)}
                                                in
                                                case o0 of {
                                                 Some m0 -> ExistT
                                                  (upd_s_mem host_function1 s
                                                    (update_list_at
                                                      (s_mems s) n0 m0))
                                                  (ExistT f0 (ExistT Nil
                                                  (ExistT hs
                                                  (R_store_packed_success
                                                  (typeof v0) v0 s n0 f0 m s0
                                                  off a m0 tp0 hs))));
                                                 None -> ExistT s (ExistT f0
                                                  (ExistT (Cons AI_trap Nil)
                                                  (ExistT hs
                                                  (R_store_packed_failure
                                                  (typeof v0) v0 s n0 f0 m s0
                                                  off a tp0 hs))))};
                                               None ->
                                                let {
                                                 o0 = store m
                                                        (n_of_uint i32m s0)
                                                        off (bits v0)
                                                        (t_length
                                                          (typeof v0))}
                                                in
                                                case o0 of {
                                                 Some m0 -> ExistT
                                                  (upd_s_mem host_function1 s
                                                    (update_list_at
                                                      (s_mems s) n0 m0))
                                                  (ExistT f0 (ExistT Nil
                                                  (ExistT hs (R_store_success
                                                  (typeof v0) v0 s n0 f0 m0
                                                  s0 a off m hs))));
                                                 None -> ExistT s (ExistT f0
                                                  (ExistT (Cons AI_trap Nil)
                                                  (ExistT hs (R_store_failure
                                                  (typeof v0) v0 s n0 f0 m s0
                                                  off a hs))))}};
                                             None -> false_rect}};
                                         _ -> false_rect}) t __ __ __ __ __
                                        __ __) t) T_i32 __;
                                 Cons _ _ -> false_rect}}}) ts3 __) ts4 __)
                        bes0 __ __ __) c0 __ __)) (Cons T_i32 (Cons t Nil)))
                  ts3) ts4 __) bes0) c0) (\c0 _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons BI_current_memory Nil) (\ts3 ts4 _ ->
              eq_rect Nil (\_ ->
                eq_rect (Cons T_i32 Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil ->
                       eq_rect_r
                         (upd_label
                           (upd_local_return c1 (map0 typeof (f_locs f0))
                             ret1) lab0) (\_ _ ->
                         eq_rect (Cons BI_current_memory Nil) (\_ _ _ ->
                           eq_rect Nil (\_ ->
                             eq_rect (Cons T_i32 Nil) (\_ ->
                               let {
                                n = mem_context_store host_function1 s
                                      (f_inst f0) c1}
                               in
                               case n of {
                                ExistT n0 _ ->
                                 let {o = nth_error (s_mems s) n0} in
                                 case o of {
                                  Some m -> ExistT s (ExistT f0 (ExistT (Cons
                                   (AI_basic (BI_const (VAL_int32
                                   (int_of_Z i32m
                                     (of_nat1 (nat_of_bin (mem_size m)))))))
                                   Nil) (ExistT hs (R_current_memory n0 f0 m
                                   (mem_size m) s hs))));
                                  None -> false_rect}}) ts3 __) ts4 __) bes0
                           __ __ __) c0 __ __;
                      Cons _ _ -> false_rect})) Nil) ts3) ts4 __) bes0) c0)
          (\c0 _ lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (Cons BI_grow_memory Nil) (\ts3 ts4 _ ->
              eq_rect (Cons T_i32 Nil) (\_ ->
                eq_rect (Cons T_i32 Nil) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inr
                    (case vcs0 of {
                      Nil -> false_rect;
                      Cons v vcs1 ->
                       case vcs1 of {
                        Nil ->
                         eq_rect (typeof v)
                           (eq_rect_r
                             (upd_label
                               (upd_local_return c1 (map0 typeof (f_locs f0))
                                 ret1) lab0) (\_ _ ->
                             eq_rect (Cons BI_grow_memory Nil) (\_ _ _ ->
                               eq_rect (Cons T_i32 Nil) (\_ ->
                                 eq_rect (Cons T_i32 Nil) (\_ ->
                                   let {
                                    n = mem_context_store host_function1 s
                                          (f_inst f0) c1}
                                   in
                                   case n of {
                                    ExistT n0 _ ->
                                     let {o = nth_error (s_mems s) n0} in
                                     case o of {
                                      Some m ->
                                       case v of {
                                        VAL_int32 s0 -> ExistT s (ExistT f0
                                         (ExistT (Cons (AI_basic (BI_const
                                         (VAL_int32 int32_minus_one))) Nil)
                                         (ExistT hs (R_grow_memory_failure n0
                                         f0 m (mem_size m) s s0 hs))));
                                        _ -> false_rect};
                                      None -> false_rect}}) ts3 __) ts4 __)
                               bes0 __ __ __) c0 __ __) T_i32;
                        Cons _ _ -> false_rect}})) (Cons T_i32 Nil)) ts3) ts4
                __) bes0) c0) (\c0 lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect Nil (\ts3 ts4 _ ->
              eq_rect Nil (\_ ->
                eq_rect Nil (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0) (Inl __) Nil) ts3) ts4 __) bes0)
            c0)
          (\c0 es e t1s t2s t3s hType2 iHHType1 hType3 iHHType2 lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect (app es (Cons e Nil)) (\ts3 ts4 _ ->
              eq_rect_r ts4 (\_ ->
                eq_rect_r ts3 (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0)
                    (eq_rect_r
                      (upd_label
                        (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
                        lab0) (\hType4 hType5 iHHType3 iHHType4 _ ->
                      eq_rect (app es (Cons e Nil)) (\_ _ _ ->
                        eq_rect_r ts4 (\iHHType5 hType6 _ ->
                          eq_rect_r ts3 (\iHHType6 _ hType7 ->
                            eq_rect (map0 typeof vcs0)
                              (\_ iHHType7 hType8 _ ->
                              let {
                               _evar_0_ = \_ ->
                                let {
                                 _evar_0_ = \_ ->
                                  let {
                                   s0 = iHHType7 lab0 ret1 f0 c1 __ __ es __
                                          __ __ t2s (map0 typeof vcs0) __
                                          vcs0 __}
                                  in
                                  case s0 of {
                                   Inl _ ->
                                    let {i = const_es_exists (to_e_list es)}
                                    in
                                    case i of {
                                     ExistT cs _ ->
                                      eq_rect_r (to_b_list (v_to_e_list cs))
                                        (\iHHType8 _ _ _ _ ->
                                        let {
                                         _evar_0_ = \_ ->
                                          let {
                                           _evar_0_ = \_ ->
                                            eq_rect_r
                                              (cat (map0 typeof vcs0)
                                                (map0 typeof cs))
                                              (\iHHType9 _ _ ->
                                              let {
                                               s1 = iHHType9 lab0 ret1 f0 c1
                                                      __ __ (Cons e Nil) __
                                                      __ __ ts3
                                                      (cat (map0 typeof vcs0)
                                                        (map0 typeof cs)) __
                                                      (cat vcs0 cs) __}
                                              in
                                              case s1 of {
                                               Inl _ -> Inl __;
                                               Inr s2 ->
                                                case s2 of {
                                                 ExistT es' hReduce -> Inr
                                                  (let {
                                                    _evar_0_ = let {
                                                                _evar_0_ = ExistT
                                                                 es'
                                                                 (let {
                                                                   _evar_0_ = 
                                                                    eq_rect_r
                                                                    (v_to_e_list
                                                                    (cat vcs0
                                                                    cs))
                                                                    hReduce
                                                                    (cat
                                                                    (v_to_e_list
                                                                    vcs0)
                                                                    (v_to_e_list
                                                                    cs))}
                                                                  in
                                                                  eq_rect_r
                                                                    (cat
                                                                    (cat
                                                                    (v_to_e_list
                                                                    vcs0)
                                                                    (v_to_e_list
                                                                    cs))
                                                                    (to_e_list
                                                                    (Cons e
                                                                    Nil)))
                                                                    _evar_0_
                                                                    (cat
                                                                    (v_to_e_list
                                                                    vcs0)
                                                                    (cat
                                                                    (v_to_e_list
                                                                    cs)
                                                                    (to_e_list
                                                                    (Cons e
                                                                    Nil)))))}
                                                               in
                                                               eq_rect_r
                                                                 (v_to_e_list
                                                                   cs)
                                                                 _evar_0_
                                                                 (to_e_list
                                                                   (to_b_list
                                                                    (v_to_e_list
                                                                    cs)))}
                                                   in
                                                   eq_rect_r
                                                     (cat
                                                       (to_e_list
                                                         (to_b_list
                                                           (v_to_e_list cs)))
                                                       (to_e_list (Cons e
                                                         Nil))) _evar_0_
                                                     (to_e_list
                                                       (app
                                                         (to_b_list
                                                           (v_to_e_list cs))
                                                         (Cons e Nil))))}})
                                              t2s iHHType6 iHHType8 hType7}
                                          in
                                          eq_rect_r (v_to_e_list cs) _evar_0_
                                            (to_e_list
                                              (to_b_list (v_to_e_list cs)))
                                            __}
                                        in
                                        eq_rect_r (v_to_e_list cs) _evar_0_
                                          (to_e_list
                                            (to_b_list (v_to_e_list cs))) __)
                                        es iHHType7 hType8 __ __ __};
                                   Inr s1 ->
                                    case s1 of {
                                     ExistT s' s2 ->
                                      case s2 of {
                                       ExistT vs' s3 ->
                                        case s3 of {
                                         ExistT es' s4 ->
                                          case s4 of {
                                           ExistT hs' hReduce -> Inr
                                            (let {
                                              _evar_0_ = ExistT s' (ExistT
                                               vs' (ExistT
                                               (cat es'
                                                 (to_e_list (Cons e Nil)))
                                               (ExistT hs'
                                               (let {
                                                 _evar_0_ = reduce_composition_right
                                                              host_function1
                                                              host_instance1
                                                              s f0
                                                              (cat
                                                                (v_to_e_list
                                                                  vcs0)
                                                                (to_e_list
                                                                  es))
                                                              (to_e_list
                                                                (Cons e Nil))
                                                              s' vs' es' hs
                                                              hs' hReduce}
                                                in
                                                eq_rect_r
                                                  (cat
                                                    (cat (v_to_e_list vcs0)
                                                      (to_e_list es))
                                                    (to_e_list (Cons e Nil)))
                                                  _evar_0_
                                                  (cat (v_to_e_list vcs0)
                                                    (cat (to_e_list es)
                                                      (to_e_list (Cons e
                                                        Nil))))))))}
                                             in
                                             eq_rect_r
                                               (cat (to_e_list es)
                                                 (to_e_list (Cons e Nil)))
                                               _evar_0_
                                               (to_e_list
                                                 (app es (Cons e Nil))))}}}}}}
                                in
                                eq_rect_r
                                  (cat (to_e_list es)
                                    (to_e_list (Cons e Nil))) _evar_0_
                                  (to_e_list (app es (Cons e Nil))) __}
                              in
                              eq_rect_r
                                (cat (to_e_list es) (to_e_list (Cons e Nil)))
                                _evar_0_ (to_e_list (app es (Cons e Nil))) __)
                              ts4 __ iHHType5 hType6 __) t3s iHHType4 __
                            hType5) t1s iHHType3 hType4 __) bes0 __ __ __) c0
                      hType2 hType3 iHHType1 iHHType2 __) ts4) t3s) t1s __)
              bes0) c0)
          (\c0 es ts t1s t2s hType2 iHHType lab0 ret1 f0 c1 _ _ ->
          eq_rect_r
            (upd_label (upd_local_return c1 (map0 typeof (f_locs f0)) ret1)
              lab0) (\bes0 _ _ _ ->
            eq_rect_r bes0 (\ts3 ts4 _ ->
              eq_rect (app ts t1s) (\_ ->
                eq_rect (app ts t2s) (\vcs0 _ ->
                  eq_rect (map0 typeof vcs0)
                    (let {
                      _evar_0_ = \_ ->
                       let {
                        _evar_0_ = \_ ->
                         eq_rect_r
                           (upd_label
                             (upd_local_return c1 (map0 typeof (f_locs f0))
                               ret1) lab0) (\hType3 iHHType0 _ ->
                           eq_rect_r bes0 (\iHHType1 hType4 _ ->
                             eq_rect (app ts t1s) (\_ ->
                               eq_rect (app ts t2s) (\_ ->
                                 eq_rect_r
                                   (map0 typeof (drop (size0 ts) vcs0))
                                   (\_ iHHType2 _ _ ->
                                   let {
                                    s0 = iHHType2 lab0 ret1 f0 c1 __ __ bes0
                                           __ __ __ t2s
                                           (map0 typeof
                                             (drop (size0 ts) vcs0)) __
                                           (drop (size0 ts) vcs0) __}
                                   in
                                   case s0 of {
                                    Inl _ -> Inl __;
                                    Inr s1 -> Inr
                                     (case s1 of {
                                       ExistT s' s2 ->
                                        case s2 of {
                                         ExistT f' s3 ->
                                          case s3 of {
                                           ExistT es' s4 ->
                                            case s4 of {
                                             ExistT hs' hReduce ->
                                              eq_rect
                                                (cat (take (size0 ts) vcs0)
                                                  (drop (size0 ts) vcs0))
                                                (let {
                                                  _evar_0_ = let {
                                                              _evar_0_ = ExistT
                                                               s' (ExistT f'
                                                               (ExistT
                                                               (cat
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    ts) vcs0))
                                                                 es') (ExistT
                                                               hs'
                                                               (reduce_composition_left
                                                                 host_function1
                                                                 host_instance1
                                                                 s
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    ts) vcs0))
                                                                 f0
                                                                 (cat
                                                                   (v_to_e_list
                                                                    (drop
                                                                    (size0
                                                                    ts) vcs0))
                                                                   (to_e_list
                                                                    bes0)) s'
                                                                 f' es' hs
                                                                 hs' hReduce))))}
                                                             in
                                                             eq_rect
                                                               (cat
                                                                 (v_to_e_list
                                                                   (take
                                                                    (size0
                                                                    ts) vcs0))
                                                                 (cat
                                                                   (v_to_e_list
                                                                    (drop
                                                                    (size0
                                                                    ts) vcs0))
                                                                   (to_e_list
                                                                    bes0)))
                                                               _evar_0_
                                                               (cat
                                                                 (cat
                                                                   (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    ts) vcs0))
                                                                   (v_to_e_list
                                                                    (drop
                                                                    (size0
                                                                    ts) vcs0)))
                                                                 (to_e_list
                                                                   bes0))}
                                                 in
                                                 eq_rect
                                                   (cat
                                                     (v_to_e_list
                                                       (take (size0 ts) vcs0))
                                                     (v_to_e_list
                                                       (drop (size0 ts) vcs0)))
                                                   _evar_0_
                                                   (v_to_e_list
                                                     (cat
                                                       (take (size0 ts) vcs0)
                                                       (drop (size0 ts) vcs0))))
                                                vcs0}}}})}) t1s hType4
                                   iHHType1 __ __) ts3 __) ts4 __) es
                             iHHType0 hType3 __) c0 hType2 iHHType __}
                       in
                       eq_rect (map0 typeof (drop (size0 ts) vcs0)) _evar_0_
                         (drop (size0 ts) (map0 typeof vcs0)) __}
                     in
                     eq_rect (map0 typeof (take (size0 ts) vcs0)) _evar_0_
                       (take (size0 ts) (map0 typeof vcs0)) __) (app ts t1s))
                  ts3) ts4 __) es) c0) upd_label0 bes tf hType1 lab ret0 f c
          __ __ bes __ __ __ ts2 ts1 __) hType0) hType) x0 vcs __

type Br_reduceT = SigT Nat (SigT Lholed ())

type Return_reduceT = SigT Nat (SigT Lholed ())

br_reduce_decidable :: (List Administrative_instruction) -> DecidableT
                       Br_reduceT
br_reduce_decidable es =
  pickable_decidable_T
    (pickable2_weaken_T
      (lfilled_pickable_rec_gen (\n _ -> Cons (AI_basic (BI_br n)) Nil)
        (\es' lh _ n ->
        lfilled_decidable_base (Cons (AI_basic (BI_br n)) Nil) es' lh) es))

return_reduce_decidable :: (List Administrative_instruction) -> DecidableT
                           Return_reduceT
return_reduce_decidable es =
  pickable_decidable_T
    (pickable2_weaken_T
      (lfilled_pickable_rec (Cons (AI_basic BI_return) Nil) (\es' ->
        lfilled_decidable_base (Cons (AI_basic BI_return) Nil) es') es))

br_reduce_extract_vs :: Type -> Host -> Nat -> Nat -> Lholed -> (List
                        Administrative_instruction) -> (Store_record 
                        Sort) -> T_context -> (List Value_type) ->
                        Result_type -> E_typing -> SigT
                        (List Administrative_instruction) (SigT Lholed ())
br_reduce_extract_vs host_function1 host_instance1 n k lh es s c ts ts2 x =
  let {
   x0 = \k0 lh0 es0 lI ->
    case lfilled_Ind_Equivalent k0 lh0 es0 lI of {
     Pair x0 _ -> x0}}
  in
  let {hLF = x0 n lh (Cons (AI_basic (BI_br (addn n k))) Nil) es __} in
  let {gen_x = Cons (AI_basic (BI_br (addn n k))) Nil} in
  lfilledInd_rect (\vs es0 es' _ host_instance2 k0 _ ->
    solution_left (Cons (AI_basic (BI_br (addn O k0))) Nil)
      (\es'0 _ host_instance3 s0 c0 ts3 ts0 hType _ ->
      let {
       hType0 = e_composition_typing host_function1 s0 c0 vs
                  (cat (Cons (AI_basic (BI_br (addn O k0))) Nil) es'0) Nil
                  ts3 hType}
      in
      case hType0 of {
       ExistT ts1 s1 ->
        case s1 of {
         ExistT t1s s2 ->
          case s2 of {
           ExistT t2s s3 ->
            case s3 of {
             ExistT t3s p ->
              case p of {
               Pair _ p1 ->
                case p1 of {
                 Pair _ p2 ->
                  case p2 of {
                   Pair h3 h4 ->
                    let {
                     h5 = e_composition_typing host_function1 s0 c0 (Cons
                            (AI_basic (BI_br (addn O k0))) Nil) es'0 t3s t2s
                            h4}
                    in
                    case h5 of {
                     ExistT ts4 s4 ->
                      case s4 of {
                       ExistT t1s0 s5 ->
                        case s5 of {
                         ExistT _ s6 ->
                          case s6 of {
                           ExistT t3s0 p3 ->
                            case p3 of {
                             Pair _ p4 ->
                              case p4 of {
                               Pair _ p5 ->
                                case p5 of {
                                 Pair h6 _ ->
                                  eq_rect_r (cat ts4 t1s0) (\h7 ->
                                    case ts1 of {
                                     Nil ->
                                      case t1s of {
                                       Nil ->
                                        let {
                                         _evar_0_ = \h8 ->
                                          let {
                                           h9 = et_to_bet host_function1 s0
                                                  c0 (Cons (AI_basic (BI_br
                                                  k0)) Nil) (Tf t1s0 t3s0)
                                                  (unsafeCoerce (Pair (ExistT
                                                    (BI_br k0) __) __)) h8}
                                          in
                                          let {
                                           h10 = break_typing host_function1
                                                   host_instance3 k0 c0 t1s0
                                                   t3s0 h9}
                                          in
                                          case h10 of {
                                           ExistT ts5 s7 ->
                                            case s7 of {
                                             ExistT ts3' _ ->
                                              eq_rect_r
                                                (cat (unsafeCoerce ts3')
                                                  (unsafeCoerce ts5))
                                                (\h11 ->
                                                let {
                                                 _evar_0_ = \_ ->
                                                  eq_rect_r
                                                    (unsafeCoerce ts5)
                                                    (eq_rect_r
                                                      (unsafeCoerce ts5)
                                                      (\_ _ ->
                                                      let {
                                                       h12 = et_to_bet
                                                               host_function1
                                                               s0 c0 vs (Tf
                                                               Nil
                                                               (cat ts4
                                                                 (cat
                                                                   (unsafeCoerce
                                                                    ts3')
                                                                   (unsafeCoerce
                                                                    ts5))))
                                                               (const_list_is_basic
                                                                 vs) h11}
                                                      in
                                                      let {
                                                       i = const_es_exists vs}
                                                      in
                                                      case i of {
                                                       ExistT vs' _ ->
                                                        eq_rect_r
                                                          (v_to_e_list vs')
                                                          (\_ ->
                                                          let {
                                                           _evar_0_ = \_ ->
                                                            eq_rect
                                                              (cat
                                                                (take
                                                                  (size0
                                                                    (cat
                                                                    (unsafeCoerce
                                                                    ts4)
                                                                    ts3'))
                                                                  vs')
                                                                (drop
                                                                  (size0
                                                                    (cat
                                                                    (unsafeCoerce
                                                                    ts4)
                                                                    ts3'))
                                                                  vs'))
                                                              (ExistT
                                                              (v_to_e_list
                                                                (drop
                                                                  (size0
                                                                    (cat
                                                                    (unsafeCoerce
                                                                    ts4)
                                                                    ts3'))
                                                                  vs'))
                                                              (ExistT
                                                              (LH_base
                                                              (v_to_e_list
                                                                (take
                                                                  (size0
                                                                    (cat
                                                                    (unsafeCoerce
                                                                    ts4)
                                                                    ts3'))
                                                                  vs')) es'0)
                                                              __)) vs'}
                                                          in
                                                          eq_rect_r
                                                            (cat
                                                              (cat
                                                                (unsafeCoerce
                                                                  ts4) ts3')
                                                              (unsafeCoerce
                                                                ts5))
                                                            _evar_0_
                                                            (cat
                                                              (unsafeCoerce
                                                                ts4)
                                                              (cat ts3'
                                                                (unsafeCoerce
                                                                  ts5))) __)
                                                          vs h12}) ts0 __ __)
                                                    ts0}
                                                in
                                                eq_rect_r (Some ts0) _evar_0_
                                                  (nth_error (tc_label c0)
                                                    k0) __) t1s0 h7}}}
                                        in
                                        eq_rect_r k0 _evar_0_ (addn O k0) h6;
                                       Cons _ _ -> false_rect};
                                     Cons _ _ -> false_rect}) t3s h3}}}}}}}}}}}}}})
      es0 es' __ host_instance2)
    (\k0 vs n0 es' _ es'' es0 lI _ hLF0 iHHLF host_instance2 k1 _ ->
    solution_left (Cons (AI_basic (BI_br (addn (S k0) k1))) Nil)
      (\lI0 _ _ iHHLF0 host_instance3 s0 c0 ts3 ts0 hType _ ->
      let {
       hType0 = e_composition_typing host_function1 s0 c0 vs
                  (cat (Cons (AI_label n0 es' lI0) Nil) es'') Nil ts3 hType}
      in
      case hType0 of {
       ExistT ts1 s1 ->
        case s1 of {
         ExistT t1s s2 ->
          case s2 of {
           ExistT t2s s3 ->
            case s3 of {
             ExistT t3s p ->
              case p of {
               Pair _ p1 ->
                case p1 of {
                 Pair _ p2 ->
                  case p2 of {
                   Pair h3 h4 ->
                    let {
                     h5 = e_composition_typing host_function1 s0 c0 (Cons
                            (AI_label n0 es' lI0) Nil) es'' t3s t2s h4}
                    in
                    case h5 of {
                     ExistT ts4 s4 ->
                      case s4 of {
                       ExistT t1s0 s5 ->
                        case s5 of {
                         ExistT _ s6 ->
                          case s6 of {
                           ExistT t3s0 p3 ->
                            case p3 of {
                             Pair _ p4 ->
                              case p4 of {
                               Pair _ p5 ->
                                case p5 of {
                                 Pair h6 h7 ->
                                  eq_rect_r (cat ts4 t1s0) (\_ ->
                                    let {
                                     h8 = label_typing host_function1 s0 c0
                                            n0 es' lI0 t1s0 t3s0 h6}
                                    in
                                    case h8 of {
                                     ExistT ts5 s7 ->
                                      case s7 of {
                                       ExistT t1s1 p6 ->
                                        case p6 of {
                                         Pair _ p7 ->
                                          case p7 of {
                                           Pair _ p8 ->
                                            case p8 of {
                                             Pair h9 _ ->
                                              eq_rect_r (cat t1s0 t1s1)
                                                (\_ ->
                                                eq_rect (length ts5)
                                                  (case ts1 of {
                                                    Nil ->
                                                     case t1s of {
                                                      Nil ->
                                                       let {
                                                        s8 = iHHLF0
                                                               host_instance3
                                                               (S k1) __ s0
                                                               (upd_label c0
                                                                 (cat (Cons
                                                                   ts5 Nil)
                                                                   (tc_label
                                                                    c0)))
                                                               t1s1 ts0 h9 __}
                                                       in
                                                       case s8 of {
                                                        ExistT x1 h ->
                                                         case h of {
                                                          ExistT lh2 _ ->
                                                           eq_rect
                                                             (addn k0 (S k1))
                                                             (ExistT x1
                                                             (ExistT (LH_rec
                                                             vs (length ts5)
                                                             es' lh2 es'')
                                                             __))
                                                             (addn (S k0) k1)}};
                                                      Cons _ _ -> false_rect};
                                                    Cons _ _ -> false_rect})
                                                  n0) t3s0 h7}}}}}) t3s h3}}}}}}}}}}}}}})
      es0 lI __ hLF0 iHHLF host_instance2) n lh gen_x es hLF host_instance1 k
    __ s c ts2 ts x __

return_reduce_extract_vs :: Type -> Host -> Nat -> Lholed -> (List
                            Administrative_instruction) -> (Store_record
                            Sort) -> T_context -> (List Value_type) ->
                            Result_type -> E_typing -> SigT
                            (List Administrative_instruction)
                            (SigT Lholed ())
return_reduce_extract_vs host_function1 host_instance1 n lh es s c ts ts2 x =
  let {
   x0 = \k lh0 es0 lI ->
    case lfilled_Ind_Equivalent k lh0 es0 lI of {
     Pair x0 _ -> x0}}
  in
  let {hLF = x0 n lh (Cons (AI_basic BI_return) Nil) es __} in
  let {gen_x = Cons (AI_basic BI_return) Nil} in
  lfilledInd_rect (\vs es0 es' _ _ ->
    solution_left (Cons (AI_basic BI_return) Nil)
      (\es'0 _ s0 c0 ts3 ts0 hType _ ->
      let {
       hType0 = e_composition_typing host_function1 s0 c0 vs
                  (cat (Cons (AI_basic BI_return) Nil) es'0) Nil ts3 hType}
      in
      case hType0 of {
       ExistT ts1 s1 ->
        case s1 of {
         ExistT t1s s2 ->
          case s2 of {
           ExistT t2s s3 ->
            case s3 of {
             ExistT t3s p ->
              case p of {
               Pair _ p1 ->
                case p1 of {
                 Pair _ p2 ->
                  case p2 of {
                   Pair h3 h4 ->
                    let {
                     h5 = e_composition_typing host_function1 s0 c0 (Cons
                            (AI_basic BI_return) Nil) es'0 t3s t2s h4}
                    in
                    case h5 of {
                     ExistT ts4 s4 ->
                      case s4 of {
                       ExistT t1s0 s5 ->
                        case s5 of {
                         ExistT _ s6 ->
                          case s6 of {
                           ExistT t3s0 p3 ->
                            case p3 of {
                             Pair _ p4 ->
                              case p4 of {
                               Pair _ p5 ->
                                case p5 of {
                                 Pair h6 _ ->
                                  eq_rect_r (cat ts4 t1s0) (\h7 ->
                                    case ts1 of {
                                     Nil ->
                                      case t1s of {
                                       Nil ->
                                        let {
                                         h8 = et_to_bet host_function1 s0 c0
                                                (Cons (AI_basic BI_return)
                                                Nil) (Tf t1s0 t3s0)
                                                (unsafeCoerce (Pair (ExistT
                                                  BI_return __) __)) h6}
                                        in
                                        let {
                                         h9 = return_typing host_function1
                                                host_instance1 c0 t1s0 t3s0
                                                h8}
                                        in
                                        case h9 of {
                                         ExistT ts5 s7 ->
                                          case s7 of {
                                           ExistT ts2' _ ->
                                            eq_rect_r (cat ts2' ts5) (\h10 ->
                                              let {
                                               _evar_0_ = \_ ->
                                                eq_rect_r ts5
                                                  (eq_rect_r ts5 (\_ _ ->
                                                    let {
                                                     h11 = et_to_bet
                                                             host_function1
                                                             s0 c0 vs (Tf Nil
                                                             (cat ts4
                                                               (cat ts2' ts5)))
                                                             (const_list_is_basic
                                                               vs) h10}
                                                    in
                                                    let {
                                                     i = const_es_exists vs}
                                                    in
                                                    case i of {
                                                     ExistT vs' _ ->
                                                      eq_rect_r
                                                        (v_to_e_list vs')
                                                        (\_ ->
                                                        let {
                                                         _evar_0_ = \_ ->
                                                          eq_rect
                                                            (cat
                                                              (take
                                                                (size0
                                                                  (cat ts4
                                                                    ts2'))
                                                                vs')
                                                              (drop
                                                                (size0
                                                                  (cat ts4
                                                                    ts2'))
                                                                vs')) (ExistT
                                                            (v_to_e_list
                                                              (drop
                                                                (size0
                                                                  (cat ts4
                                                                    ts2'))
                                                                vs')) (ExistT
                                                            (LH_base
                                                            (v_to_e_list
                                                              (take
                                                                (size0
                                                                  (cat ts4
                                                                    ts2'))
                                                                vs')) es'0)
                                                            __)) vs'}
                                                        in
                                                        eq_rect_r
                                                          (cat (cat ts4 ts2')
                                                            ts5) _evar_0_
                                                          (cat ts4
                                                            (cat ts2' ts5))
                                                          __) vs h11}) ts0 __
                                                    __) ts0}
                                              in
                                              eq_rect_r (Some ts0) _evar_0_
                                                (tc_return c0) __) t1s0 h7}};
                                       Cons _ _ -> false_rect};
                                     Cons _ _ -> false_rect}) t3s h3}}}}}}}}}}}}}})
      es0 es' __) (\_ vs n0 es' _ es'' es0 lI _ hLF0 iHHLF _ ->
    solution_left (Cons (AI_basic BI_return) Nil)
      (\lI0 _ _ iHHLF0 s0 c0 ts3 ts0 hType _ ->
      let {
       hType0 = e_composition_typing host_function1 s0 c0 vs
                  (cat (Cons (AI_label n0 es' lI0) Nil) es'') Nil ts3 hType}
      in
      case hType0 of {
       ExistT ts1 s1 ->
        case s1 of {
         ExistT t1s s2 ->
          case s2 of {
           ExistT t2s s3 ->
            case s3 of {
             ExistT t3s p ->
              case p of {
               Pair _ p1 ->
                case p1 of {
                 Pair _ p2 ->
                  case p2 of {
                   Pair h3 h4 ->
                    let {
                     h5 = e_composition_typing host_function1 s0 c0 (Cons
                            (AI_label n0 es' lI0) Nil) es'' t3s t2s h4}
                    in
                    case h5 of {
                     ExistT ts4 s4 ->
                      case s4 of {
                       ExistT t1s0 s5 ->
                        case s5 of {
                         ExistT _ s6 ->
                          case s6 of {
                           ExistT t3s0 p3 ->
                            case p3 of {
                             Pair _ p4 ->
                              case p4 of {
                               Pair _ p5 ->
                                case p5 of {
                                 Pair h6 h7 ->
                                  eq_rect_r (cat ts4 t1s0) (\_ ->
                                    let {
                                     h8 = label_typing host_function1 s0 c0
                                            n0 es' lI0 t1s0 t3s0 h6}
                                    in
                                    case h8 of {
                                     ExistT ts5 s7 ->
                                      case s7 of {
                                       ExistT t1s1 p6 ->
                                        case p6 of {
                                         Pair _ p7 ->
                                          case p7 of {
                                           Pair _ p8 ->
                                            case p8 of {
                                             Pair h9 _ ->
                                              eq_rect_r (cat t1s0 t1s1)
                                                (\_ ->
                                                eq_rect (length ts5)
                                                  (case ts1 of {
                                                    Nil ->
                                                     case t1s of {
                                                      Nil ->
                                                       let {
                                                        s8 = iHHLF0 __ s0
                                                               (upd_label c0
                                                                 (cat (Cons
                                                                   ts5 Nil)
                                                                   (tc_label
                                                                    c0)))
                                                               t1s1 ts0 h9 __}
                                                       in
                                                       case s8 of {
                                                        ExistT x1 s9 ->
                                                         case s9 of {
                                                          ExistT lh2 _ ->
                                                           ExistT x1 (ExistT
                                                           (LH_rec vs
                                                           (length ts5) es'
                                                           lh2 es'') __)}};
                                                      Cons _ _ -> false_rect};
                                                    Cons _ _ -> false_rect})
                                                  n0) t3s0 h7}}}}}) t3s h3}}}}}}}}}}}}}})
      es0 lI __ hLF0 iHHLF) n lh gen_x es hLF __ s c ts2 ts x __

host_application_exists :: Type -> Host -> Sort -> (Store_record Sort) ->
                           Function_type -> Sort -> (List Value) -> SigT 
                           Sort
                           (SigT (Option (Prod (Store_record Sort) Result))
                           ())
host_application_exists =
  Prelude.error "AXIOM TO BE REALIZED"

t_progress_e :: Type -> Host -> (Store_record Sort) -> T_context -> T_context
                -> Frame -> (List Value) -> (List Administrative_instruction)
                -> Function_type -> Result_type -> Result_type -> (List
                (List Value_type)) -> (Option (List Value_type)) -> Sort ->
                E_typing -> Store_typing -> Sum Terminal_form
                (SigT (Store_record Sort)
                (SigT Frame
                (SigT (List Administrative_instruction) (SigT Sort Reduce))))
t_progress_e host_function1 host_instance1 s c c' f vcs es tf ts1 ts2 lab ret0 hs x x0 =
  e_typing_ind' host_function1
    (\s0 c0 bes tf0 hType f0 c'0 vcs0 ts3 ts4 lab0 ret1 hs0 _ _ _ _ hST _ _ ->
    eq_rect_r (Tf ts3 ts4) (\hType0 ->
      eq_rect_r
        (upd_label (upd_local_return c'0 (map0 typeof (f_locs f0)) ret1)
          lab0) (\hType1 ->
        eq_rect (map0 typeof vcs0) (\hType2 ->
          let {
           hType3 = t_progress_be host_function1 host_instance1 c'0 bes
                      (map0 typeof vcs0) ts4 vcs0 lab0 ret1 s0 f0 hs0 hST
                      hType2}
          in
          case hType3 of {
           Inl _ -> Inl Left;
           Inr s1 -> Inr s1}) ts3 hType1) c0 hType0) tf0 hType)
    (\s0 c0 es0 e t1s t2s t3s hType1 iHHType1 hType2 iHHType2 f0 c'0 vcs0 ts3 ts4 lab0 ret1 hs0 _ _ _ _ hST _ _ ->
    eq_rect_r ts3 (\_ ->
      eq_rect_r ts4
        (eq_rect_r
          (upd_label (upd_local_return c'0 (map0 typeof (f_locs f0)) ret1)
            lab0) (\hType3 iHHType3 hType4 iHHType4 ->
          eq_rect (map0 typeof vcs0) (\_ _ ->
            eq_rect_r (map0 typeof vcs0) (\iHHType5 hType5 _ ->
              eq_rect_r ts4 (\iHHType6 hType6 _ ->
                let {
                 s1 = iHHType5 f0 c'0 vcs0 (map0 typeof vcs0) t2s lab0 ret1
                        hs0 __ __ __ __ hST __ __}
                in
                case s1 of {
                 Inl t ->
                  case t of {
                   Left ->
                    let {
                     hType7 = et_to_bet host_function1 s0
                                (upd_label
                                  (upd_local_return c'0
                                    (map0 typeof (f_locs f0)) ret1) lab0) es0
                                (Tf (map0 typeof vcs0) t2s)
                                (const_list_is_basic es0) hType5}
                    in
                    let {hC2 = const_es_exists es0} in
                    case hC2 of {
                     ExistT esv _ ->
                      eq_rect_r (v_to_e_list esv) (\_ iHHType7 _ _ ->
                        eq_rect_r (cat (map0 typeof vcs0) (map0 typeof esv))
                          (\hType8 iHHType8 _ ->
                          let {
                           s2 = iHHType8 f0 c'0 (cat vcs0 esv)
                                  (cat (map0 typeof vcs0) (map0 typeof esv))
                                  ts4 lab0 ret1 hs0 __ __ __ __ hST __ __}
                          in
                          case s2 of {
                           Inl t0 ->
                            case t0 of {
                             Left -> Inl Left;
                             Right ->
                              let {
                               _evar_0_ = \_ ->
                                case vcs0 of {
                                 Nil ->
                                  case esv of {
                                   Nil -> Inl
                                    (eq_rect_r AI_trap (\_ _ _ _ ->
                                      terminal_trap) e iHHType8 hType8 __ __);
                                   Cons _ _ -> false_rect};
                                 Cons _ _ -> false_rect}}
                              in
                              eq_rect
                                (cat (v_to_e_list vcs0) (v_to_e_list esv))
                                _evar_0_ (v_to_e_list (cat vcs0 esv)) __};
                           Inr s3 ->
                            let {
                             _evar_0_ = \s4 ->
                              let {_evar_0_ = \s5 -> Inr s5} in
                              eq_rect
                                (cat (v_to_e_list vcs0)
                                  (cat (v_to_e_list esv) (Cons e Nil)))
                                _evar_0_
                                (cat
                                  (cat (v_to_e_list vcs0) (v_to_e_list esv))
                                  (Cons e Nil)) s4}
                            in
                            eq_rect
                              (cat (v_to_e_list vcs0) (v_to_e_list esv))
                              _evar_0_ (v_to_e_list (cat vcs0 esv)) s3}) t2s
                          hType6 iHHType6 iHHType7) es0 hType7 iHHType5 __ __};
                   Right ->
                    case vcs0 of {
                     Nil ->
                      case es0 of {
                       Nil -> false_rect;
                       Cons a es1 ->
                        case es1 of {
                         Nil ->
                          eq_rect_r AI_trap
                            (eq_rect_r AI_trap (\_ _ _ _ _ -> Inr (ExistT s0
                              (ExistT f0 (ExistT (Cons AI_trap Nil) (ExistT
                              hs0 (R_simple (Cons AI_trap (Cons e Nil)) (Cons
                              AI_trap Nil) s0 f0 hs0 (Rs_trap (Cons AI_trap
                              (Cons e Nil)) (LH_base Nil (Cons e Nil)))))))))
                              a hType5 iHHType5 __ __ __) a;
                         Cons _ _ -> false_rect}};
                     Cons _ _ -> false_rect}};
                 Inr s2 ->
                  case s2 of {
                   ExistT s' s3 ->
                    case s3 of {
                     ExistT f' s4 ->
                      case s4 of {
                       ExistT es' s5 ->
                        case s5 of {
                         ExistT hs' hReduce -> Inr (ExistT s' (ExistT f'
                          (ExistT (cat es' (Cons e Nil)) (ExistT hs' (R_label
                          s0 f0 (cat (v_to_e_list vcs0) es0)
                          (cat (v_to_e_list vcs0) (cat es0 (Cons e Nil))) s'
                          f' es' (cat es' (Cons e Nil)) O (LH_base Nil (Cons
                          e Nil)) hs0 hs' hReduce)))))}}}}}) t3s iHHType4
                hType4 __) t1s iHHType3 hType3 __) ts3 __ __) c0 hType1
          iHHType1 hType2 iHHType2) t3s) t1s __)
    (\s0 c0 es0 ts t1s t2s hType iHHType f0 c'0 vcs0 ts3 ts4 lab0 ret1 hs' _ _ _ _ hST _ _ ->
    eq_rect (cat ts t1s) (\_ ->
      eq_rect (cat ts t2s)
        (eq_rect_r
          (upd_label (upd_local_return c'0 (map0 typeof (f_locs f0)) ret1)
            lab0) (\hType0 iHHType0 ->
          eq_rect (map0 typeof vcs0) (\_ _ ->
            eq_rect (cat ts t2s) (\_ ->
              let {
               _evar_0_ = \_ ->
                let {
                 _evar_0_ = \_ ->
                  let {
                   _evar_0_ = let {
                               _evar_0_ = let {
                                           s1 = iHHType0 f0 c'0
                                                  (drop (size0 ts) vcs0) t1s
                                                  t2s lab0 ret1 hs' __ __ __
                                                  __ hST __ __}
                                          in
                                          case s1 of {
                                           Inl t ->
                                            case t of {
                                             Left -> Inl Left;
                                             Right ->
                                              eq_rect_r
                                                (map0 typeof
                                                  (drop (size0 ts) vcs0))
                                                (\iHHType1 hType1 _ ->
                                                eq_rect_r (Cons AI_trap Nil)
                                                  (\_ _ _ _ ->
                                                  let {
                                                   _evar_0_ = let {
                                                               l = drop
                                                                    (size0
                                                                    ts) vcs0}
                                                              in
                                                              case l of {
                                                               Nil ->
                                                                let {
                                                                 _evar_0_ = \_ ->
                                                                  let {
                                                                   _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    case vcs0 of {
                                                                     Nil ->
                                                                    Inl
                                                                    terminal_trap;
                                                                     Cons v
                                                                    vcs1 ->
                                                                    Inr
                                                                    (ExistT
                                                                    s0
                                                                    (ExistT
                                                                    f0
                                                                    (ExistT
                                                                    (Cons
                                                                    AI_trap
                                                                    Nil)
                                                                    (ExistT
                                                                    hs'
                                                                    (R_simple
                                                                    (cat
                                                                    (v_to_e_list
                                                                    (Cons v
                                                                    vcs1))
                                                                    (Cons
                                                                    AI_trap
                                                                    Nil))
                                                                    (Cons
                                                                    AI_trap
                                                                    Nil) s0
                                                                    f0 hs'
                                                                    (reduce_trap_left
                                                                    (v_to_e_list
                                                                    (Cons v
                                                                    vcs1))))))))}}
                                                                    in
                                                                    eq_rect_r
                                                                    (v_to_e_list
                                                                    vcs0)
                                                                    _evar_0_
                                                                    (cat
                                                                    (v_to_e_list
                                                                    vcs0)
                                                                    Nil)}
                                                                  in
                                                                  eq_rect
                                                                    vcs0
                                                                    _evar_0_
                                                                    (take
                                                                    (size0
                                                                    ts) vcs0)}
                                                                in
                                                                eq_rect_r
                                                                  (take
                                                                    (size0
                                                                    ts) vcs0)
                                                                  _evar_0_
                                                                  (cat
                                                                    (take
                                                                    (size0
                                                                    ts) vcs0)
                                                                    Nil) __;
                                                               Cons _ _ ->
                                                                false_rect}}
                                                  in
                                                  eq_rect_r Nil _evar_0_
                                                    (v_to_e_list
                                                      (drop (size0 ts) vcs0)))
                                                  es0 hType1 iHHType1 __ __)
                                                t1s iHHType0 hType0 __};
                                           Inr s2 ->
                                            case s2 of {
                                             ExistT s' s3 ->
                                              case s3 of {
                                               ExistT f' s4 ->
                                                case s4 of {
                                                 ExistT es' s5 ->
                                                  case s5 of {
                                                   ExistT hs'' hReduce -> Inr
                                                    (ExistT s' (ExistT f'
                                                    (ExistT
                                                    (cat
                                                      (v_to_e_list
                                                        (take (size0 ts)
                                                          vcs0)) es') (ExistT
                                                    hs''
                                                    (let {
                                                      _evar_0_ = reduce_composition_left
                                                                   host_function1
                                                                   host_instance1
                                                                   s0
                                                                   (v_to_e_list
                                                                    (take
                                                                    (size0
                                                                    ts) vcs0))
                                                                   f0
                                                                   (cat
                                                                    (v_to_e_list
                                                                    (drop
                                                                    (size0
                                                                    ts) vcs0))
                                                                    es0) s'
                                                                   f' es' hs'
                                                                   hs''
                                                                   hReduce}
                                                     in
                                                     eq_rect
                                                       (cat
                                                         (v_to_e_list
                                                           (take (size0 ts)
                                                             vcs0))
                                                         (cat
                                                           (v_to_e_list
                                                             (drop (size0 ts)
                                                               vcs0)) es0))
                                                       _evar_0_
                                                       (cat
                                                         (cat
                                                           (v_to_e_list
                                                             (take (size0 ts)
                                                               vcs0))
                                                           (v_to_e_list
                                                             (drop (size0 ts)
                                                               vcs0))) es0))))))}}}}}}
                              in
                              eq_rect
                                (cat (v_to_e_list (take (size0 ts) vcs0))
                                  (v_to_e_list (drop (size0 ts) vcs0)))
                                _evar_0_
                                (v_to_e_list
                                  (cat (take (size0 ts) vcs0)
                                    (drop (size0 ts) vcs0)))}
                  in
                  eq_rect_r
                    (cat (take (size0 ts) vcs0) (drop (size0 ts) vcs0))
                    _evar_0_ vcs0}
                in
                eq_rect (map0 typeof (drop (size0 ts) vcs0)) _evar_0_
                  (drop (size0 ts) (map0 typeof vcs0)) __}
              in
              eq_rect (map0 typeof (take (size0 ts) vcs0)) _evar_0_
                (take (size0 ts) (map0 typeof vcs0)) __) ts4 __) ts3 __ __)
          c0 hType iHHType) ts4) ts3 __)
    (\s0 _ _ f0 _ vcs0 _ _ _ _ hs0 _ _ _ _ _ _ _ ->
    case vcs0 of {
     Nil -> Inl terminal_trap;
     Cons v vcs1 -> Inr (ExistT s0 (ExistT f0 (ExistT (Cons AI_trap Nil)
      (ExistT hs0 (R_simple
      (cat (v_to_e_list (Cons v vcs1)) (Cons AI_trap Nil)) (Cons AI_trap Nil)
      s0 f0 hs0 (reduce_trap_left (v_to_e_list (Cons v vcs1))))))))})
    (\s0 _ n f0 es0 ts hType iHHType _ f1 _ vcs0 ts3 ts4 _ _ hs0 _ _ _ _ hST _ _ ->
    eq_rect Nil (\_ ->
      eq_rect_r ts4
        (eq_rect (length ts) (\_ _ ->
          eq_rect (map0 typeof vcs0) (\_ _ ->
            eq_rect_r ts4 (\hType0 iHHType0 _ _ _ ->
              case vcs0 of {
               Nil -> Inr
                (let {d = return_reduce_decidable es0} in
                 case d of {
                  Inl hEMT ->
                   case hType0 of {
                    Mk_s_typing s1 f2 es1 rs ts0 c0 c1 x1 x2 ->
                     eq_rect_r s0 (\_ ->
                       eq_rect_r (Some ts4) (\_ ->
                         eq_rect_r f0 (\_ ->
                           eq_rect_r es0 (\_ ->
                             eq_rect_r ts4 (\_ _ x3 _ ->
                               eq_rect_r (upd_return c1 (Some ts4)) (\x4 ->
                                 case hEMT of {
                                  ExistT n0 s2 ->
                                   case s2 of {
                                    ExistT lh _ ->
                                     let {
                                      hLF = return_reduce_extract_vs
                                              host_function1 host_instance1
                                              n0 lh es0 s0
                                              (upd_return c1 (Some ts4)) ts4
                                              ts4 x4}
                                     in
                                     case hLF of {
                                      ExistT cs s3 ->
                                       case s3 of {
                                        ExistT lh' _ -> ExistT s0 (ExistT f1
                                         (ExistT cs (ExistT hs0 (R_simple
                                         (Cons (AI_local (length ts4) f0 es0)
                                         Nil) cs s0 f1 hs0 (Rs_return
                                         (length ts4) n0 cs es0 lh' f0)))))}}}})
                                 c0 x3) ts0) es1) f2) rs) s1 __ __ __ __ x1
                       __ x2 __};
                  Inr hEMF ->
                   let {s1 = iHHType0 hs0 hST __ __} in
                   case s1 of {
                    Inl h ->
                     case h of {
                      Inl _ -> ExistT s0 (ExistT f1 (ExistT es0 (ExistT hs0
                       (R_simple (Cons (AI_local (length ts4) f0 es0) Nil)
                       es0 s0 f1 hs0 (Rs_local_const es0 (length ts4) f0)))));
                      Inr _ ->
                       eq_rect_r (Cons AI_trap Nil) (\_ _ _ _ _ -> ExistT s0
                         (ExistT f1 (ExistT (Cons AI_trap Nil) (ExistT hs0
                         (R_simple (Cons (AI_local (length ts4) f0 (Cons
                         AI_trap Nil)) Nil) (Cons AI_trap Nil) s0 f1 hs0
                         (Rs_local_trap (length ts4) f0)))))) es0 iHHType0
                         hType0 __ __ hEMF};
                    Inr h ->
                     case h of {
                      ExistT s' s2 ->
                       case s2 of {
                        ExistT f0' s3 ->
                         case s3 of {
                          ExistT es' s4 ->
                           case s4 of {
                            ExistT hs' hReduce -> ExistT s' (ExistT f1
                             (ExistT (Cons (AI_local (length ts4) f0' es')
                             Nil) (ExistT hs' (R_local s0 f0 es0 s' f0' es'
                             (length ts4) f1 hs0 hs' hReduce))))}}}}}});
               Cons _ _ -> false_rect}) ts hType iHHType __ __ __) ts3 __ __)
          n __ __) ts) ts3 __)
    (\s0 a _ cl tf0 _ hType f0 _ vcs0 ts3 ts4 _ _ hs0 _ _ _ _ _ _ _ ->
    case hType of {
     Cl_typing_native i s1 c0 c'0 ts t1s t2s es0 tf1 x1 ->
      eq_rect_r s0 (\_ ->
        eq_rect (FC_func_native i tf1 ts es0) (\_ ->
          eq_rect (Tf t1s t2s) (\_ _ _ x2 ->
            eq_rect_r (Tf ts3 ts4) (\hType0 _ ->
              eq_rect (map0 typeof vcs0) (\hType1 _ ->
                eq_rect_r (Tf t1s t2s) (\_ ->
                  eq_rect_r
                    (upd_local_label_return c0
                      (cat (tc_local c0) (cat t1s ts))
                      (cat (Cons t2s Nil) (tc_label c0)) (Some t2s)) (\x3 ->
                    eq_rect (FC_func_native i (Tf t1s t2s) ts es0)
                      (\_ hType2 ->
                      eq_rect_r (map0 typeof vcs0) (\_ ->
                        eq_rect_r ts4
                          (eq_rect_r (map0 typeof vcs0) (\_ hType3 x4 _ ->
                            eq_rect_r ts4 (\_ _ _ _ -> Inr (ExistT s0 (ExistT
                              f0 (ExistT (Cons (AI_local (length ts4)
                              (Build_frame (cat vcs0 (n_zeros ts)) i) (Cons
                              (AI_basic (BI_block (Tf Nil ts4) es0)) Nil))
                              Nil) (ExistT hs0 (R_invoke_native a
                              (FC_func_native i (Tf (map0 typeof vcs0) ts4)
                              ts es0) (map0 typeof vcs0) ts4 ts es0
                              (v_to_e_list vcs0) vcs0 (length vcs0)
                              (length ts4) (length ts) (n_zeros ts) s0 f0
                              (Build_frame (cat vcs0 (n_zeros ts)) i) i
                              hs0)))))) t2s hType3 __ __ x4) t1s __ hType2 x3
                            __) t2s) t1s __) cl __ hType1) c'0 x2) tf1 __)
                ts3 hType0 __) tf0 hType __) tf0) cl) s1 __ __ __ __ __ x1;
     Cl_typing_host s1 tf1 h ->
      eq_rect_r s0 (\_ ->
        eq_rect (FC_func_host tf1 h) (\_ ->
          eq_rect_r tf0
            (eq_rect_r (Tf ts3 ts4) (\hType0 _ ->
              eq_rect (map0 typeof vcs0) (\hType1 _ ->
                eq_rect (FC_func_host tf1 h) (\_ hType2 ->
                  eq_rect_r (Tf (map0 typeof vcs0) ts4) (\_ _ -> Inr
                    (let {
                      hApply = host_application_exists host_function1
                                 host_instance1 hs0 s0 (Tf (map0 typeof vcs0)
                                 ts4) h vcs0}
                     in
                     case hApply of {
                      ExistT hs' s2 ->
                       case s2 of {
                        ExistT res _ ->
                         case res of {
                          Some opres ->
                           case opres of {
                            Pair p r -> ExistT p (ExistT f0 (ExistT
                             (result_to_stack r) (ExistT hs'
                             (R_invoke_host_success a (FC_func_host (Tf
                             (map0 typeof vcs0) ts4) h) h (map0 typeof vcs0)
                             ts4 (v_to_e_list vcs0) vcs0 (length ts4)
                             (length vcs0) s0 p r f0 hs0 hs'))))};
                          None -> ExistT s0 (ExistT f0 (ExistT
                           (cat (v_to_e_list vcs0) (Cons (AI_invoke a) Nil))
                           (ExistT hs' (R_invoke_host_diverge a (FC_func_host
                           (Tf (map0 typeof vcs0) ts4) h) (map0 typeof vcs0)
                           ts4 h (v_to_e_list vcs0) vcs0 (length vcs0)
                           (length ts4) s0 f0 hs0 hs'))))}}})) tf1 __ hType2)
                  cl __ hType1) ts3 hType0 __) tf0 hType __) tf1) cl) s1 __
        __})
    (\s0 c0 e0s es0 ts t2s n hType1 iHHType1 hType2 iHHType2 _ f0 c'0 vcs0 ts3 ts4 lab0 ret1 hs0 _ _ _ _ hST _ _ ->
    eq_rect Nil (\_ ->
      eq_rect_r ts4
        (eq_rect (length ts) (\_ _ ->
          eq_rect_r
            (upd_label (upd_local_return c'0 (map0 typeof (f_locs f0)) ret1)
              lab0) (\hType3 iHHType3 hType4 iHHType4 ->
            eq_rect (map0 typeof vcs0) (\_ _ ->
              eq_rect_r ts4 (\iHHType5 hType5 _ _ _ ->
                case vcs0 of {
                 Nil ->
                  let {
                   _evar_0_ = \hType6 ->
                    let {d = br_reduce_decidable es0} in
                    case d of {
                     Inl hEMT ->
                      case hEMT of {
                       ExistT n0 s1 ->
                        case s1 of {
                         ExistT lh _ -> Inr
                          (let {
                            lF = br_reduce_extract_vs host_function1
                                   host_instance1 n0 O lh es0 s0
                                   (upd_label
                                     (upd_local_return c'0
                                       (map0 typeof (f_locs f0)) ret1) (Cons
                                     ts lab0)) ts ts4 hType6}
                           in
                           case lF of {
                            ExistT cs s2 ->
                             case s2 of {
                              ExistT lh' _ ->
                               let {
                                _evar_0_ = \_ -> ExistT s0 (ExistT f0 (ExistT
                                 (cat cs e0s) (ExistT hs0 (R_simple (Cons
                                 (AI_label (length ts) e0s es0) Nil)
                                 (cat cs e0s) s0 f0 hs0 (Rs_br (length ts) cs
                                 e0s n0 es0 lh')))))}
                               in
                               eq_rect_r n0 _evar_0_ (addn n0 O) __}})}};
                     Inr hEMF ->
                      let {
                       s1 = iHHType5 f0 c'0 Nil (map0 typeof Nil) ts4 (Cons
                              ts lab0) ret1 hs0 __ __ __ __ hST __ __}
                      in
                      case s1 of {
                       Inl hTerm ->
                        let {
                         hTerm0 = terminal_form_v_e (v_to_e_list Nil) es0
                                    hTerm}
                        in
                        case hTerm0 of {
                         Left -> Inr (ExistT s0 (ExistT f0 (ExistT es0
                          (ExistT hs0 (R_simple (Cons (AI_label (length ts)
                          e0s es0) Nil) es0 s0 f0 hs0 (Rs_label_const
                          (length ts) e0s es0))))));
                         Right -> Inr
                          (eq_rect_r (Cons AI_trap Nil) (\_ _ _ _ _ -> ExistT
                            s0 (ExistT f0 (ExistT (Cons AI_trap Nil) (ExistT
                            hs0 (R_simple (Cons (AI_label (length ts) e0s
                            (Cons AI_trap Nil)) Nil) (Cons AI_trap Nil) s0 f0
                            hs0 (Rs_label_trap (length ts) e0s)))))) es0
                            iHHType5 __ __ hType6 hEMF)};
                       Inr hReduce ->
                        case hReduce of {
                         ExistT s' s2 ->
                          case s2 of {
                           ExistT f' s3 ->
                            case s3 of {
                             ExistT es' s4 ->
                              case s4 of {
                               ExistT hs' hReduce0 -> Inr (ExistT s' (ExistT
                                f' (ExistT (Cons (AI_label (length ts) e0s
                                es') Nil) (ExistT hs' (R_label s0 f0 es0
                                (Cons (AI_label (length ts) e0s es0) Nil) s'
                                f' es' (Cons (AI_label (length ts) e0s es')
                                Nil) (S O) (LH_rec Nil (length ts) e0s
                                (LH_base Nil Nil) Nil) hs0 hs' hReduce0)))))}}}}}}}
                  in
                  eq_rect_r
                    (upd_label
                      (upd_local_return c'0 (map0 typeof (f_locs f0)) ret1)
                      (cat (Cons ts Nil)
                        (tc_label
                          (upd_label
                            (upd_local_return c'0 (map0 typeof (f_locs f0))
                              ret1) lab0)))) _evar_0_
                    (upd_label
                      (upd_label
                        (upd_local_return c'0 (map0 typeof (f_locs f0)) ret1)
                        lab0)
                      (cat (Cons ts Nil)
                        (tc_label
                          (upd_label
                            (upd_local_return c'0 (map0 typeof (f_locs f0))
                              ret1) lab0)))) hType5;
                 Cons _ _ -> false_rect}) t2s iHHType4 hType4 iHHType3 hType3
                __) ts3 __ __) c0 hType1 iHHType1 hType2 iHHType2) n __ __)
        t2s) ts3 __)
    (\s0 f0 _ rs ts c0 c1 hFT _ hType iHHType _ hs0 hST _ _ ->
    case hFT of {
     Mk_frame_typing s1 i tvs c2 f1 ->
      eq_rect_r s0 (\_ ->
        eq_rect_r f0 (\_ ->
          eq_rect (upd_local c2 (cat (tc_local c2) tvs)) (\_ _ _ ->
            eq_rect_r (upd_return c1 rs) (\hType0 iHHType0 ->
              eq_rect (f_inst f0) (\_ ->
                eq_rect (map0 typeof (f_locs f0)) (\_ ->
                  eq_rect
                    (upd_local c2
                      (cat (tc_local c2) (map0 typeof (f_locs f0))))
                    (\_ iHHType1 _ ->
                    let {
                     s2 = iHHType1 f0 c2 Nil Nil ts (tc_label c2) rs hs0 __
                            __ __ __ hST __ __}
                    in
                    case s2 of {
                     Inl hTerm ->
                      case hTerm of {
                       Left -> Inl (Inl __);
                       Right -> Inl (Inr __)};
                     Inr hReduce -> Inr hReduce}) c1 hFT iHHType0 hType0) tvs
                  __) i __) c0 hType iHHType) c1) f1) s1 __ __ __ __ __}) s c
    es tf x f c' vcs ts1 ts2 lab ret0 hs __ __ __ __ x0 __ __

t_progress :: Type -> Host -> (Store_record Sort) -> Frame -> (List
              Administrative_instruction) -> (List Value_type) -> Sort ->
              Config_typing -> Sum Terminal_form
              (SigT (Store_record Sort)
              (SigT Frame
              (SigT (List Administrative_instruction) (SigT Sort Reduce))))
t_progress host_function1 host_instance1 s f es ts hs hType =
  case hType of {
   Mk_config_typing s0 f0 es0 ts0 x hstyping ->
    eq_rect_r s (\_ ->
      eq_rect_r f (\_ ->
        eq_rect_r es (\_ ->
          eq_rect_r ts (\x0 hstyping0 ->
            case hstyping0 of {
             Mk_s_typing s1 f1 es1 rs ts1 c c0 hftyping hetyping ->
              eq_rect_r s (\_ ->
                eq_rect_r None (\_ ->
                  eq_rect_r f (\_ ->
                    eq_rect_r es (\_ ->
                      eq_rect_r ts (\hftyping0 _ hetyping0 _ ->
                        case hftyping0 of {
                         Mk_frame_typing s2 i tvs c1 f2 ->
                          eq_rect_r s (\_ ->
                            eq_rect_r f (\_ ->
                              eq_rect (upd_local c1 (cat (tc_local c1) tvs))
                                (\_ _ _ ->
                                eq_rect_r (upd_return c0 None) (\hetyping1 ->
                                  eq_rect (f_inst f) (\_ ->
                                    eq_rect (map0 typeof (f_locs f)) (\_ ->
                                      eq_rect
                                        (upd_local c1
                                          (cat (tc_local c1)
                                            (map0 typeof (f_locs f))))
                                        (\_ hetyping2 ->
                                        t_progress_e host_function1
                                          host_instance1 s
                                          (upd_return
                                            (upd_local c1
                                              (cat (tc_local c1)
                                                (map0 typeof (f_locs f))))
                                            None) c1 f Nil es (Tf Nil ts) Nil
                                          ts Nil None hs hetyping2 x0) c0
                                        hftyping0 hetyping1) tvs __) i __) c
                                  hetyping0) c0) f2) s2 __ __ __ __ __}) ts1)
                      es1) f1) rs) s1 __ __ __ __ hftyping __ hetyping __})
            ts0) es0) f0) s0 __ __ __ x hstyping}

host_function0 :: Type
host_function0 =
  Prelude.error "AXIOM TO BE REALIZED"

host_instance0 :: Host
host_instance0 =
  Prelude.error "AXIOM TO BE REALIZED"

host_state0 :: Type
host_state0 =
  host_state host_function0 host_instance0

t_progress0 :: Type -> Host -> (Store_record Sort) -> Frame -> (List
               Administrative_instruction) -> (List Value_type) -> Sort ->
               Config_typing -> Sum Terminal_form
               (SigT (Store_record Sort)
               (SigT Frame
               (SigT (List Administrative_instruction) (SigT Sort Reduce))))
t_progress0 =
  t_progress

i32_of_Z :: Z -> Value
i32_of_Z z =
  VAL_int32 (int_of_Z i32m z)

add_2_7 :: List Administrative_instruction
add_2_7 =
  Cons (AI_basic (BI_const (i32_of_Z (Zpos (XO XH))))) (Cons (AI_basic
    (BI_const (i32_of_Z (Zpos (XI (XI XH)))))) (Cons (AI_basic (BI_binop
    T_i32 (Binop_i0 BOI_add))) Nil))

add_2_7_bis :: List Basic_instruction
add_2_7_bis =
  Cons (BI_const (i32_of_Z (Zpos (XO XH)))) (Cons (BI_const
    (i32_of_Z (Zpos (XI (XI XH))))) (Cons (BI_binop T_i32 (Binop_i0 BOI_add))
    Nil))

type Store_record2 = Store_record Sort

emp_store_record :: Store_record2
emp_store_record =
  Build_store_record Nil Nil Nil Nil

emp_instance :: Instance
emp_instance =
  Build_instance Nil Nil Nil Nil Nil

emp_frame :: Frame
emp_frame =
  Build_frame Nil emp_instance

emp_context :: T_context
emp_context =
  Build_t_context Nil Nil Nil Nil Nil Nil Nil None

h_be_typing_add_2_7 :: Be_typing
h_be_typing_add_2_7 =
  Bet_composition emp_context (Cons (BI_const (i32_of_Z (Zpos (XO XH))))
    (Cons (BI_const (i32_of_Z (Zpos (XI (XI XH))))) Nil)) (BI_binop T_i32
    (Binop_i0 BOI_add)) Nil (Cons T_i32 (Cons T_i32 Nil)) (Cons T_i32 Nil)
    (Bet_composition emp_context (Cons (BI_const (i32_of_Z (Zpos (XO XH))))
    Nil) (BI_const (i32_of_Z (Zpos (XI (XI XH))))) Nil (Cons T_i32 Nil) (Cons
    T_i32 (Cons T_i32 Nil)) (Bet_const emp_context (i32_of_Z (Zpos (XO XH))))
    (Bet_weakening emp_context (Cons (BI_const
    (i32_of_Z (Zpos (XI (XI XH))))) Nil) (Cons T_i32 Nil) Nil (Cons T_i32
    Nil) (Bet_const emp_context (i32_of_Z (Zpos (XI (XI XH))))))) (Bet_binop
    emp_context T_i32 (Binop_i0 BOI_add))

h_config_typing_add_2_7 :: Config_typing
h_config_typing_add_2_7 =
  Mk_config_typing emp_store_record emp_frame add_2_7 (Cons T_i32 Nil)
    (unsafeCoerce (Pair Forall_nil __)) (Mk_s_typing emp_store_record
    emp_frame add_2_7 None (Cons T_i32 Nil) emp_context emp_context
    (Mk_frame_typing emp_store_record emp_instance Nil emp_context emp_frame)
    (Ety_a emp_store_record emp_context add_2_7_bis (Tf Nil (Cons T_i32 Nil))
    h_be_typing_add_2_7))

ts_add_2_7 :: List Value_type
ts_add_2_7 =
  Cons T_i32 Nil

