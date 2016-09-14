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

data TCtxt = TNil Ident
           | TCns TCtxt (Ident, Typ) (Ident, Typ)
           | TTgt TCtxt 

printCtxt :: TCtxt -> String           
printCtxt (TNil id) = "(" ++ printTree id ++ " : *)"
printCtxt (TCns tc (tId, tFrm) (fId, fFrm)) =
  printCtxt tc ++ " " ++ printTree (Tele tId tFrm) ++ " " ++ printTree (Tele fId fFrm)
printCtxt (TTgt tc) = printCtxt tc

instance Show TCtxt where
  -- Possibly print the head too?
  show = printCtxt
  
lookupTc :: TCtxt -> Ident -> Typ
lookupTc (TNil id) id' | id == id' = TStar
lookupTc (TNil id) id' | otherwise = error $ "Tree lookup failed for: " ++ printTree id'
lookupTc (TCns tc (tId, tFrm) (fId, fFrm)) id' | tId == id' = tFrm
lookupTc (TCns tc (tId, tFrm) (fId, fFrm)) id' | fId == id' = fFrm
lookupTc (TCns tc (tId, tFrm) (fId, fFrm)) id' | otherwise = lookupTc tc id'
lookupTc (TTgt tc) id' = lookupTc tc id'

marker :: TCtxt -> (Ident, Typ)
marker (TNil id) = (id, TStar)
marker (TCns _ _ f) = f
marker (TTgt tc) =
  case marker tc of
    (mId, TStar) -> error "Target of object marker"
    (mId, TArr frm _ (EVar tgt)) -> (tgt, frm)
    _ -> error "Internal error"
    
type Gamma = [(Ident, D)]
type Delta = [(Ident, Typ)]

data TCEnv = TCEnv { gma :: Gamma }

-- Yeah, you should make a real empty environment
emptyEnv :: TCEnv
emptyEnv = TCEnv [] 

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
--  Operations on Types and Trees
--

typeDim :: Typ -> Int
typeDim TStar = 0
typeDim (TArr t _ _) = typeDim t + 1

ctxtDim :: TCtxt -> Int
ctxtDim (TNil id) = 0
ctxtDim (TCns tc (tId, tFrm) (fId, fFrm)) = max (typeDim fFrm) (ctxtDim tc)
ctxtDim (TTgt tc) = ctxtDim tc  
  
source :: Int -> TCtxt -> TCtxt
source i (TNil id) = TNil id
source i (TCns tc (tId, tFrm) (fId, fFrm)) | i <= typeDim tFrm = source i tc
source i (TCns tc (tId, tFrm) (fId, fFrm)) | i > typeDim tFrm = TCns (source i tc) (tId, tFrm) (fId, fFrm)
source i (TTgt tc) = TTgt (source i tc)

target :: Int -> TCtxt -> TCtxt
target i (TNil id) = TNil id
target i (TCns tc (tId, tFrm) (fId, fFrm)) | i <= typeDim tFrm = target i (rewindTo tId tFrm tc)

  where rewindTo tgtId tgtFrm (TNil id) = TNil tgtId
        rewindTo tgtId tgtFrm (TTgt tc) = rewindTo tgtId tgtFrm tc
        rewindTo tgtId tgtFrm (TCns tc' (pId, pFrm) (qId, qFrm)) | tgtFrm == qFrm = TCns tc' (pId, pFrm) (tgtId, tgtFrm)
        rewindTo tgtId tgtFrm (TCns tc' (pId, pFrm) (qId, qFrm)) | otherwise = rewindTo tgtId tgtFrm tc'
                              
  -- This is trickier.  We want to rewind to the place where the source
  -- was added, necessarily, I suppose as a filler, and replace that source
  -- extension with the value of the target.
                                           

target i (TCns tc (tId, tFrm) (fId, fFrm)) | i > typeDim tFrm = TCns (target i tc) (tId, tFrm) (fId, fFrm)
target i (TTgt tc) = TTgt (target i tc)

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
    (Tele x TStar) : ps        -> do tctx <- checkTree (TNil x) ps 
                                     debug $ "Tree okay for " ++ show id
                                     debug $ "Result: " ++ show tctx
                                     debug $ "Source: " ++ show (source (ctxtDim tctx - 1) tctx)
                                     debug $ "Target: " ++ show (target (ctxtDim tctx - 1) tctx)
                                     return ()
checkDecl (Def id pms ty exp) = return ()

typEq :: Typ -> Typ -> TCM ()
typEq t0 t1 = if t0 == t1 then
                return ()
              else throwError $ "Unequal types: " ++ show t0 ++ ", " ++ show t1
                               
-- Okay, this is not quite right.  You have to recurse of the target
-- of the marker until you get a match or hit the botom.
checkTree :: TCtxt -> [Tele] -> TCM TCtxt
checkTree tc [] = return tc
checkTree tc (_:[]) = throwError $ "Context parity violation"
checkTree tc tl@((Tele tId tFrm):(Tele fId fFrm):ps) =
  case (marker tc) of
    (mId, mFrm) | tFrm == mFrm -> let expected = TArr tFrm (EVar mId) (EVar tId)
                                  in if (fFrm == expected)         -- The case of raising a dimension
                                     then checkTree (TCns tc (tId, tFrm) (fId, fFrm)) ps
                                     else throwError $
                                          "Error while checking " ++ printTree fId ++ "\n" ++
                                          "Expected: " ++ printTree expected ++ "\n" ++
                                          "Found: " ++ printTree fFrm

    -- Try to extend with respect to a target
    (mId, mFrm) | otherwise -> checkTree (TTgt tc) tl
                                                      

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
