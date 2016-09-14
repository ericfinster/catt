--
--  TypeChecker.hs - Catt Typechecker
--

module TypeChecker where

import Control.Monad.Except
import Control.Monad.Reader

import Syntax.AbsCatt
import Syntax.PrintCatt

--
--  Semantic Domain
--

data D = VarD Ident
       | TypeD | StarD
       | ArrD D D D
       | PiD D (D -> D)
       | LamD (D -> D)

appD :: D -> D -> D
appD (LamD f) d = f d
  
--
--  Terms
--

data Term = Var Ident
          | Type | Star 
          | Arr Term Term Term
          | Pi Ident Term Term
          | Lam Ident Term
          | App Term Term

--
--  Evaluation and Readback
--

eval :: Term -> Rho -> D
eval Type              rho = TypeD
eval Star              rho = StarD
eval (Var id)          rho = getRho id rho
eval (Arr frm src tgt) rho = ArrD (eval frm rho) (eval src rho) (eval tgt rho)
eval (Pi id a f)       rho = PiD (eval a rho) (\d -> eval f $ UpVar rho id d)
eval (Lam id u)        rho = LamD (\d -> eval u $ UpVar rho id d)
eval (App u v)         rho = appD (eval u rho) (eval v rho)

rb :: D -> Int -> Term
rb TypeD              k = Type
rb StarD              k = Star
rb (VarD id)          k = Var id
rb (ArrD frm src tgt) k = Arr (rb frm k) (rb src k) (rb tgt k)
rb (PiD a f)          k = let id = Ident $ "RB#" ++ show k
                          in Pi id (rb a k) (rb (f $ VarD id) (k+1))
rb (LamD f)           k = let id = Ident $ "RB#" ++ show k
                          in Lam id (rb (f $ VarD id) (k+1))

--
--  Typechecking Environment
--

type Gma = [(Ident, D)]

data Rho = RNil
         | UpDef Rho Ident Term Term
         | UpVar Rho Ident D

getRho :: Ident -> Rho -> D
getRho id RNil = error $ "Environment missing id: " ++ show id
getRho id (UpDef rho id' _ tm) | id == id' = eval tm rho
getRho id (UpDef rho id' _ tm) | otherwise = getRho id rho
getRho id (UpVar rho id' d) | id == id' = d
getRho id (UpVar rho id' d) | otherwise = getRho id rho

data TCEnv = TCEnv
  { gma :: Gma
  , rho :: Rho
  , mkr :: (Ident,D)
  }

withVar :: Ident -> D -> TCEnv -> TCEnv
withVar id d (TCEnv gma rho mkr) =
  TCEnv ((id, d):gma) (UpVar rho id d) mkr

withExt :: Ident -> D -> Ident -> D -> TCEnv -> TCEnv
withExt t tD f fD (TCEnv gma rho mkr) =
  TCEnv ((f,fD):(t,tD):gma) (UpVar (UpVar rho t tD) f fD) (f,fD)

--
--  Typechecking Monad
--

type TCM = ReaderT TCEnv (ExceptT String IO)

tcLookup :: Ident -> TCM D
tcLookup id = do gma <- reader gma
                 case lookup id gma of
                   Just d -> return d
                   Nothing -> throwError $ "Unknown identifier: " ++ show id

tcEval :: Term -> TCM D
tcEval = undefined

tcExtPi :: D -> TCM (D, D -> D)
tcExtPi (PiD a f) = return (a, f)
tcExtPi _ = throwError "tcExtPi"

tcExtSrc :: Typ -> TCM (Exp, Typ)
tcExtSrc (TArr h s _) = return (s, h)
tcExtSrc typ = throwError $ "tcExtSrc: " ++ printTree typ

tcExtTgt :: Typ -> TCM (Exp, Typ)
tcExtTgt (TArr h _ t) = return (t, h)
tcExtTgt typ = throwError $ "tcExtTgt: " ++ printTree typ

--
--  Operations on Types
--

typeDim :: Typ -> Int
typeDim TStar = 0
typeDim (TArr t _ _) = typeDim t + 1

--
--  Typechecking Rules
--

checkDecls :: [Decl] -> TCM ()
checkDecls [] = return ()
checkDecls (d:ds) = return ()

checkDecl :: Decl -> TCM ()
checkDecl (Coh id pms ty) =
  case pms of
    []                         -> throwError $ "Nothing to be done in empty context"
    (Tele x (TArr _ _ _)) : ps -> throwError $ "Context cannot start with an arrow"
    (Tele x TStar) : ps        -> local (withVar x StarD) $
                                  do tm <- checkTree ps ty
                                     return undefined
checkDecl (Def id pms ty exp) = return ()

checkTree :: [Tele] -> Typ -> TCM Term
checkTree [] ty = checkT ty -- Right, this is not enough. Need coverage and src/tgt possibilities
checkTree (t:f:ps) ty = do
  m <- reader mkr
  case m of
    (mId, StarD) -> case (t, f) of
                      (Tele tId TStar, Tele fId (TArr TStar (EVar srcId) (EVar tgtId))) ->
                        if (srcId == mId && tgtId == tId)
                        then local (withExt tId StarD fId (ArrD StarD (VarD srcId) (VarD tgtId))) (checkTree ps ty)
                        else throwError $ "malformed extension"
                      _ -> throwError $ "malformed extension from base"

    (mId, ArrD frm (VarD sId) (VarD tId)) -> undefined
      case (t, f) of 

checkT :: Typ -> TCM Term
checkT t = case t of
  TStar            -> return Star
  TArr frm src tgt -> do frmT <- checkT frm
                         frmD <- tcEval frmT
                         srcT <- check src frmD
                         tgtT <- check tgt frmD
                         return $ Arr frmT srcT tgtT

check :: Exp -> D -> TCM Term
check e t = undefined

checkI :: Exp -> TCM (Term, D)
checkI e = 
  case e of
    EVar id  -> do d <- tcLookup id 
                   return (Var id, d)
    EApp u v -> do (uT, uTy) <- checkI u
                   uD <- tcEval uT
                   (a, f) <- tcExtPi uTy
                   vT <- check v a
                   return (App uT vT, f uD)
                   

-- data Exp = EApp Ident [Exp] | EVar Ident
--   deriving (Eq, Ord, Show, Read)

-- data Typ = TStar | TArr Typ Exp Exp
--   deriving (Eq, Ord, Show, Read)
