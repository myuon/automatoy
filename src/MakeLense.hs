{-# LANGUAGE GADTs, RankNTypes, TypeOperators, DataKinds, KindSignatures #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies, ScopedTypeVariables, TypeFamilies #-}
module MakeLense (
  Name(..),
  UnionT,
  Union(..),
  TypeCheck(..),
  HList(..),
  WrongType, NoSuchKey, NotEnough,
  All,

  (:<)(..),
  sinsert,
  getter,
  setter,
  lenses
  ) where
import GHC.TypeLits
import GHC.Prim (Constraint)
import Data.List (intersperse)
import Lens.Family2
import Lens.Family2.State.Lazy
import Lens.Family2.Unchecked

data (:<) (s :: Symbol) a = Tag a

instance (Show v, KnownSymbol k) => Show (k :< v) where
  show (Tag x :: k :< v) = symbolVal (Name :: Name k) ++ ":" ++ show x

data HList (xs :: [*]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

type family All (ctr :: * -> Constraint) (xs :: [*]) :: Constraint where
  All ctr '[] = ()
  All ctr (x ': xs) = (ctr x, All ctr xs)

class ShowHList (xs :: [*]) where
  showHList :: All Show xs => HList xs -> [String]

instance ShowHList '[] where
  showHList HNil = []

instance ShowHList xs => ShowHList (x ': xs) where
  showHList (HCons x xs) = show x : showHList xs

instance (All Show xs, ShowHList xs) => Show (HList xs) where
  show xs = "[" ++ (concat $ intersperse "," $ showHList xs) ++ "]"

data Union (xs :: [*]) = Union (HList xs) deriving (Show)
type UnionT (xs :: [*]) = Union (Reverse xs)

type family Snoc (xs :: [*]) y :: [*] where
  Snoc '[] y = '[y]
  Snoc (x ': xs) y = x ': Snoc xs y

type family Reverse (xs :: [*]) :: [*] where
  Reverse '[] = '[]
  Reverse (x ': xs) = Snoc (Reverse xs) x

liftHL :: (HList xs -> HList ys) -> Union xs -> Union ys
liftHL f (Union xs) = Union $ f xs

lowerU :: (Union xs -> Union ys) -> HList xs -> HList ys
lowerU f xs = (\(Union ys) -> ys) $ f (Union xs)

class SmartInsert k v (xs :: [*]) (xs' :: [*]) | k v xs -> xs' where
  sinsert :: (k :< v) -> Union xs -> Union xs'

instance SmartInsert k v '[] '[k :< v] where
  sinsert t = liftHL $ \HNil -> HCons t HNil

instance SmartInsert k v ((k :< v) ': xs) ((k :< v) ': xs) where
  sinsert t = liftHL $ \(HCons _ xs) -> HCons t xs

instance {-# OVERLAPPABLE #-} (SmartInsert k v xs xs') => SmartInsert k v (kv ': xs) (kv ': xs') where
  sinsert kv (Union (HCons x xs)) = liftHL (HCons x) $ sinsert kv $ Union xs

-- pretty error message

class TypeCheck xs xs' where
  check :: Union xs -> Union xs'

instance TypeCheck '[] '[] where
  check = liftHL $ \HNil -> HNil

instance (TypeCheck xs xs') => TypeCheck ((k :< v) ': xs) ((k :< v) ': xs')  where
  check (Union (HCons x xs)) = Union $ HCons x $ lowerU check xs

data NoSuchKey (k :: Symbol)
instance (NoSuchKey k ~ v) => TypeCheck ((k :< v) ': xs) '[]  where
  check = undefined

data WrongType (k :: Symbol) v
data ActualType v
instance {-# OVERLAPPABLE #-} (WrongType k v ~ v') => TypeCheck ((k :< v) ': xs) ((k :< v') ': xs')  where
  check = undefined

instance {-# OVERLAPPABLE #-} (NoSuchKey k ~ v') => TypeCheck ((k :< v) ': xs) ((k' :< v') ': xs')  where
  check = undefined

data NotEnough (k :: Symbol)
instance (NotEnough k ~ v) => TypeCheck '[] ((k :< v) ': xs)  where
  check = undefined

-- makeLense

data Name (s :: Symbol) = Name

class MakeLense (xs :: [*]) (s :: Symbol) out | xs s -> out where
  getter' :: Name (s :: Symbol) -> HList xs -> out
  setter' :: Name (s :: Symbol) -> (out -> out) -> HList xs -> HList xs

instance MakeLense ((k :< v) ': xs) k v where
  getter' _ (HCons (Tag v) _) = v
  setter' _ f (HCons (Tag v) xs) = HCons (Tag $ f v) xs

instance {-# OVERLAPPABLE #-} MakeLense xs syb out => MakeLense ((k :< v) ': xs) syb out where
  getter' k (HCons _ xs) = getter' k xs
  setter' k f (HCons x xs) = HCons x $ setter' k f xs

getter :: (MakeLense xs s out) => Name (s :: Symbol) -> Getter' (Union xs) out
getter syb = to $ \(Union hl) -> getter' syb hl

setter :: (MakeLense xs s out) => Name (s :: Symbol) -> Setter' (Union xs) out
setter syb = setting $ \f (Union hl) -> Union $ setter' syb f hl

lenses :: (MakeLense xs s out) => Name (s :: Symbol) -> Lens' (Union xs) out
lenses syb = lens (^. getter syb) (\u x -> set (setter syb) x u)
