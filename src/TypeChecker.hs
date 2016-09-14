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
       | AppD D D
       | LamD (D -> D)

appD :: D -> D -> D
appD (LamD f) d = f d
  
--
--  Terms
--

-- data Term = Var Ident
--           | Type | Star 
--           | Arr Term Term Term
--           | Pi Ident Term Term
--           | Lam Ident Term
--           | App Term Term

--
--  Evaluation and Readback
--

evalTyp :: Typ -> D
evalTyp TStar = StarD
evalTyp (TArr frm src tgt) = ArrD (evalTyp frm) (evalExp src) (evalExp tgt)

evalExp :: Exp -> D
evalExp (EVar id) = VarD id
evalExp (EApp u v) = AppD (evalExp u) (evalExp v)

-- eval :: Term -> Rho -> D
-- eval Type              rho = TypeD
-- eval Star              rho = StarD
-- eval (Var id)          rho = getRho id rho
-- eval (Arr frm src tgt) rho = ArrD (eval frm rho) (eval src rho) (eval tgt rho)
-- eval (Pi id a f)       rho = PiD (eval a rho) (\d -> eval f $ UpVar rho id d)
-- eval (Lam id u)        rho = LamD (\d -> eval u $ UpVar rho id d)
-- eval (App u v)         rho = appD (eval u rho) (eval v rho)

-- rb :: D -> Int -> Term
-- rb TypeD              k = Type
-- rb StarD              k = Star
-- rb (VarD id)          k = Var id
-- rb (ArrD frm src tgt) k = Arr (rb frm k) (rb src k) (rb tgt k)
-- rb (PiD a f)          k = let id = Ident $ "RB#" ++ show k
--                           in Pi id (rb a k) (rb (f $ VarD id) (k+1))
-- rb (LamD f)           k = let id = Ident $ "RB#" ++ show k
--                           in Lam id (rb (f $ VarD id) (k+1))

--
--  Typechecking Environment
--

type Gamma = [(Ident, D)]
type Delta = [(Ident, Typ)]

data TCEnv = TCEnv
  { gma :: Gamma
  , del :: Delta
  , mkr :: (Ident,Typ)
  }

-- Yeah, you should make a real empty environment
emptyEnv :: TCEnv
emptyEnv = TCEnv [] [] (Ident "", TStar)
  
startTree :: Ident -> Typ -> TCEnv -> TCEnv
startTree id typ env = TCEnv (gma env) [(id,typ)] (id, typ)
  
extendTree :: (Ident, Typ) -> (Ident, Typ) -> TCEnv -> TCEnv
extendTree t f env = TCEnv (gma env) (f:t:(del env)) f

-- withVar :: Ident -> D -> TCEnv -> TCEnv
-- withVar id d (TCEnv gma rho mkr) =
--   TCEnv ((id, d):gma) (UpVar rho id d) mkr

-- withExt :: Ident -> D -> Ident -> D -> TCEnv -> TCEnv
-- withExt t tD f fD (TCEnv gma rho mkr) =
--   TCEnv ((f,fD):(t,tD):gma) (UpVar (UpVar rho t tD) f fD) (f,fD)

--
--  Typechecking Monad
--

type TCM = ReaderT TCEnv (ExceptT String IO)

-- tcLookup :: Ident -> TCM D
-- tcLookup id = do gma <- reader gma
--                  case lookup id gma of
--                    Just d -> return d
--                    Nothing -> throwError $ "Unknown identifier: " ++ show id

-- tcExtPi :: D -> TCM (D, D -> D)
-- tcExtPi (PiD a f) = return (a, f)
-- tcExtPi _ = throwError "tcExtPi"

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
checkDecls (d:ds) = do _ <- checkDecl d
                       _ <- checkDecls ds
                       return ()

checkDecl :: Decl -> TCM ()
checkDecl (Coh id pms ty) =
  case pms of
    []                         -> throwError $ "Nothing to be done in empty context"
    (Tele x (TArr _ _ _)) : ps -> throwError $ "Context cannot start with an arrow"
    (Tele x TStar) : ps        -> local (startTree x TStar) $
                                  do _ <- checkTree ps ty
                                     debug $ "Tree okay for " ++ show id
                                     return ()
checkDecl (Def id pms ty exp) = return ()

typEq :: Typ -> Typ -> TCM ()
typEq t0 t1 = if t0 == t1 then
                return ()
              else throwError $ "Unequal types: " ++ show t0 ++ ", " ++ show t1
                               

checkTree :: [Tele] -> Typ -> TCM ()
checkTree [] ty = return ()
checkTree (_:[]) _ = throwError $ "Uneven extension length"
checkTree ((Tele tId tFrm):(Tele fId fFrm):ps) ty = do
  m <- reader mkr
  case m of
    (mId, mFrm) | tFrm == mFrm -> let expected = TArr tFrm (EVar mId) (EVar tId)
                                  in if (fFrm == expected)  -- The case of raising a dimension
                                     then continue
                                     else throwError $
                                          "Error while checking " ++ printTree fId ++ "\n" ++
                                          "Expected: " ++ printTree expected ++ "\n" ++
                                          "Found: " ++ printTree fFrm
    (mId, mFrm) | otherwise -> do (tgtId, tgtFrm) <- tcExtTgt mFrm              -- The case of continuing in the current dimension
                                  (srcId, srcFrm) <- tcExtSrc fFrm
                                  if (tgtFrm == srcFrm)
                                    then continue
                                    else throwError $
                                         "Source/target mismatch while checking " ++ printTree fId ++ "\n" ++
                                         "Src: " ++ printTree srcFrm ++ "=/=\n" ++
                                         "Tgt: " ++ printTree tgtFrm 

  where continue = local (extendTree (tId, tFrm) (fId, fFrm)) (checkTree ps ty)
  
-- checkT :: Typ -> TCM Term
-- checkT t = case t of
--   TStar            -> return Star
--   TArr frm src tgt -> do frmT <- checkT frm
--                          frmD <- tcEval frmT
--                          srcT <- check src frmD
--                          tgtT <- check tgt frmD
--                          return $ Arr frmT srcT tgtT

-- check :: Exp -> D -> TCM Term
-- check e t = undefined

-- checkI :: Exp -> TCM (Term, D)
-- checkI e = 
--   case e of
--     EVar id  -> do d <- tcLookup id 
--                    return (Var id, d)
--     EApp u v -> do (uT, uTy) <- checkI u
--                    uD <- tcEval uT
--                    (a, f) <- tcExtPi uTy
--                    vT <- check v a
--                    return (App uT vT, f uD)
                   

-- data Exp = EApp Ident [Exp] | EVar Ident
--   deriving (Eq, Ord, Show, Read)

-- data Typ = TStar | TArr Typ Exp Exp
--   deriving (Eq, Ord, Show, Read)

debug :: String -> TCM ()
debug msg = liftIO $ putStrLn msg
