{-# LANGUAGE TypeSynonymInstances #-}

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Error
import Control.Monad (foldM)
import Data.Maybe (fromMaybe)
import Data.Functor ((<$>))

type Id = String

-- Expressions

data Expr =
	Var Id |
	Ap Expr Expr |
	Abs Id Expr |
	Let Id Expr Expr |
	Rec Id Expr
		deriving (Show)

data Type =
	TVar Int |
	Arrow Type Type 
		deriving (Show, Eq, Ord)

data Scheme = 
	Scheme (Set.Set Int) Type
		deriving (Show, Eq, Ord)

type Subs = Map.Map Int Type

nullSubs = Map.empty

(@@) :: Subs -> Subs -> Subs
s2 @@ s1 = Map.map (subs s2) s1 `Map.union` s2

class Types a where
	subs :: Subs -> a -> a
	free :: a -> Set.Set Int

instance Types Type where
	subs s t = case t of
		TVar i -> fromMaybe t (Map.lookup i s)
		Arrow t1 t2 -> Arrow (subs s t1) (subs s t2)
	free t = case t of
		TVar i -> Set.singleton i
		Arrow t1 t2 -> free t1 `Set.union` free t2

instance Types Scheme where
	subs s (Scheme bs t) = Scheme bs 
		(subs (Map.filterWithKey (\k _ -> k `Set.notMember` bs) s) t)
	free (Scheme bs t) = free t Set.\\ bs

data Constraint =
	Equal Type Type |
	Implicit Type (Set.Set Int) Type |
	Explicit Type Scheme 
		deriving (Show, Eq, Ord)

instance Types Constraint where
	subs s c = case c of
		Equal t1 t2 -> Equal (subs s t1) (subs s t2)
		Implicit t1 m t2 -> Implicit (subs s t1) m (subs s t2)
		Explicit t o -> Explicit (subs s t) (subs s o)
	free = error "free Constraint"
		

data TypeCheckError =
	TypeError Type Type |
	InfiniteType Int Type
		deriving (Show, Eq)

type TI a = StateT Int (Either TypeCheckError) a

runTI :: TI a -> Either TypeCheckError a
runTI a = fst <$> runStateT a 0

fresh :: TI Type
fresh = do
	f <- get
	modify succ
	return (TVar f)

type Assumps = Set.Set (Id, Int)

bu :: Set.Set Int -> Expr -> TI (Assumps, Set.Set Constraint, Type)
bu monos e = case e of
	Var x -> do
		(TVar i) <- fresh
		return (Set.singleton (x, i), Set.empty, TVar i)
	Ap e1 e2 -> do
		fv <- fresh
		(a1, c1, t1) <- bu monos e1
		(a2, c2, t2) <- bu monos e2
		let c3 = Set.singleton (Equal t1 (Arrow t2 fv))
		return (a1 `Set.union` a2, c1 `Set.union` c2 `Set.union` c3, fv)
	Abs x e -> do
		fv@(TVar i) <- fresh
		(a, c, t) <- bu (Set.insert i monos) e
		let c2 = Set.map (\(x, t) -> Equal (TVar t) fv) 
			$ Set.filter ((== x) . fst) a
		return (Set.filter ((/= x) . fst) a, c `Set.union` c2, Arrow fv t)
	Let x e1 e2 -> do
		(a1, c1, t1) <- bu monos e1
		(a2, c2, t2) <- bu monos e2
		let a3 = a1 `Set.union` Set.filter ((/= x) . fst) a2
		let c3 = Set.map (\(x, t) -> Implicit (TVar t) monos t1) 
			$ Set.filter ((== x) . fst) a2
		return (a3, c1 `Set.union` c2 `Set.union` c3, t2)
	Rec x e -> do
		fv@(TVar i) <- fresh
		(a, c1, t) <- bu monos e
		let c2 = Set.map (\(x, t) -> Equal (TVar t) fv)
			$ Set.filter ((== x) . fst) a
		return (Set.filter ((/= x) . fst) a, c1 `Set.union` c2, t)

solve :: Set.Set Constraint -> TI Subs
solve cs = case Set.minView cs of
	Nothing -> return nullSubs
	Just (Equal t1 t2, cs) -> do
		s <- lift $ mgu t1 t2
		cs' <- solve (Set.map (subs s) cs)
		return $ cs' @@ s
	Just (Implicit t1 m t2, cs) -> 
		case (free t2 Set.\\ m) `Set.intersection` active cs of
			x | x /= Set.empty -> error $ "duno: " ++ show cs
			_ -> solve $ Set.singleton (Explicit t1 (gen m t2)) `Set.union` cs
	Just (Explicit t s, cs) -> do
		t' <- inst s
		solve $ Set.singleton (Equal t t') `Set.union` cs

gen :: Set.Set Int -> Type -> Scheme
gen m t = Scheme (free t Set.\\ m) t

inst :: Scheme -> TI Type
inst (Scheme bs t) = do
	s <- foldM go nullSubs (Set.toList bs)
	return $ subs s t
	where
		go :: Subs -> Int -> TI Subs
		go s i = do
			fv <- fresh
			return $ Map.singleton i fv @@ s


active :: Set.Set Constraint -> Set.Set Int
active cs = Set.unions $ map go (Set.toList cs)
	where
		go :: Constraint -> Set.Set Int
		go c = case c of
			Equal t1 t2 -> free t1 `Set.union` free t2
			Implicit t1 m t2 -> free t1 `Set.union` 
				(m `Set.intersection` free t2)
			Explicit t s -> free t `Set.union` free s

mgu :: Type -> Type -> Either TypeCheckError Subs
mgu t1 t2 = case (t1, t2) of
	(Arrow t1a t1r, Arrow t2a t2r) -> do
		s1 <- mgu t1a t2a
		s2 <- mgu (subs s1 t1r) (subs s1 t2r)
		return $ s2 @@ s1
	(TVar i, t) -> varBind i t
	(t, TVar i) -> varBind i t
	_ -> Left $ TypeError t1 t2
	where
		varBind :: Int -> Type -> Either TypeCheckError Subs
		varBind i t
			| t == TVar i = return nullSubs
			| i `Set.member` free t = Left $ InfiniteType i t
			| otherwise = return $ Map.singleton i t
