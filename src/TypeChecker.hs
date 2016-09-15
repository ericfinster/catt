--
--  TypeChecker.hs - Catt Typechecker
--

module TypeChecker where

import Data.Set

import Control.Monad.Except
import Control.Monad.Reader

import Syntax.AbsCatt
import Syntax.PrintCatt

import Debug.Trace

--
--  Semantic Domain
--

data D = VarD Ident | CohD Ident
       | TypeD | StarD
       | ArrD D D D
       | PiD D (D -> D)
       | AppD D D

--
--  Terms
--

data Term = Type | Star
          | Var Ident | Cohr Ident
          | Arr Term Term Term
          | Pi Ident Term Term
          | App Term Term
          deriving Eq

printTerm :: Term -> String
printTerm Type = "Type"
printTerm Star = "*"
printTerm (Var id) = printTree id
printTerm (Cohr id) = "#" ++ printTree id
printTerm (Arr frm src tgt) = printTerm frm ++ " | " ++ printTerm src ++ " -> " ++ printTerm tgt
printTerm (Pi id ty tm) = "(" ++ printTree id ++ " : " ++ printTerm ty ++ ") -> " ++ printTerm tm
printTerm (App u v) = printTerm u ++ " " ++ printTerm v

instance Show Term where
  show = printTerm
  
--
--  Evaluation and Readback
--

typToTerm :: Typ -> Term
typToTerm TStar = Star
typToTerm (TArr frm src tgt) = Arr (typToTerm frm) (expToTerm src) (expToTerm tgt)

expToTerm :: Exp -> Term
expToTerm (EVar id) = Var id
expToTerm (ECoh id) = Cohr id
expToTerm (EApp u v) = App (expToTerm u) (expToTerm v)

typToDom :: Typ -> D
typToDom TStar = StarD
typToDom (TArr frm src tgt) = ArrD (typToDom frm) (expToDom src) (expToDom tgt)

expToDom :: Exp -> D
expToDom (EVar id) = VarD id
expToDom (ECoh id) = CohD id
expToDom (EApp u v) = AppD (expToDom u) (expToDom v)


eval :: Term -> Rho -> D
eval Type              rho = TypeD
eval Star              rho = StarD
eval (Var id)          rho = getRho id rho
eval (Cohr id)         rho = CohD id
eval (Arr frm src tgt) rho = ArrD (eval frm rho) (eval src rho) (eval tgt rho)
eval (Pi id a f)       rho = PiD (eval a rho) (\d -> eval f $ UpVar rho id d)
eval (App u v)         rho = AppD (eval u rho) (eval v rho)

rb :: D -> Int -> Term
rb TypeD              k = Type
rb StarD              k = Star
rb (VarD id)          k = Var id
rb (CohD id)          k = Cohr id
rb (ArrD frm src tgt) k = Arr (rb frm k) (rb src k) (rb tgt k)
rb (PiD a f)          k = let id = Ident $ "RB#" ++ show k
                          in Pi id (rb a k) (rb (f $ VarD id) (k+1))
rb (AppD u v)         k = App (rb u k) (rb v k)                             

--
--  Typechecking Environment
--

data Rho = RNil
         | UpCoh Rho Ident 
         | UpVar Rho Ident D

getRho :: Ident -> Rho -> D
getRho id' RNil = error $ "Unknown id in environment: " ++ show (printTree id')
getRho id' (UpCoh rho id) | id == id' = CohD id
getRho id' (UpCoh rho id) | otherwise = getRho id' rho
getRho id' (UpVar rho id d) | id == id' = d
getRho id' (UpVar rho id d) | otherwise = getRho id' rho
         
lRho :: Rho -> Int
lRho RNil = 0
lRho (UpCoh rho _) = lRho rho
lRho (UpVar rho _ _) = lRho rho + 1

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

abstractTree :: TCtxt -> Term -> Term
abstractTree (TNil id) tm = Pi id Star tm
abstractTree (TTgt tc) tm = abstractTree tc tm
abstractTree (TCns tc (tId, tFrm) (fId, fFrm)) tm = 
  let fTy = typToTerm fFrm
      tTy = typToTerm tFrm
  in abstractTree tc $ Pi tId tTy $ Pi fId fTy tm
  
type Gamma = [(Ident, D)]
data TCEnv = TCEnv { gma :: Gamma
                   , rho :: Rho
                   }

appendTree :: TCtxt -> Gamma -> Gamma
appendTree (TNil id) gma = (id,StarD):gma
appendTree (TCns tc (tId,tFrm) (fId, fFrm)) gma =
  let fTy = typToDom fFrm
      tTy = typToDom tFrm
  in (fId,fTy):(tId,tTy):(appendTree tc gma)
appendTree (TTgt tc) gma = appendTree tc gma

withVar :: Ident -> Typ -> TCEnv -> TCEnv
withVar id typ (TCEnv gma rho) = TCEnv ((id,typToDom typ):gma)  (UpVar rho id (VarD id))

withTree :: TCtxt -> TCEnv -> TCEnv
withTree (TNil id) = withVar id TStar
withTree (TTgt tc) = withTree tc
withTree (TCns tc (tId,tFrm) (fId, fFrm)) =
  (withVar fId fFrm) . (withVar tId tFrm) . (withTree tc)

-- Yeah, you should make a real empty environment
emptyEnv :: TCEnv
emptyEnv = TCEnv [] RNil

--
--  Typechecking Monad
--

type TCM = ReaderT TCEnv (ExceptT String IO)

tcLookup :: Ident -> TCM D
tcLookup id = do gma <- reader gma
                 case lookup id gma of
                   Just ty -> return ty
                   Nothing -> throwError $
                              "Unknown identifier: " ++ show id ++ 
                              "\nIds: " ++ show (fmap fst gma)

tcDepth :: TCM Int
tcDepth = reader (lRho . rho)

tcPrintDom :: D -> TCM ()
tcPrintDom d = do k <- tcDepth
                  debug $ show (rb d k)
                    
tcEval :: Term -> TCM D
tcEval t = do rho <- reader rho
              return (eval t rho)
  
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
--  Operations on Types and Trees
--

typeDim :: Typ -> Int
typeDim TStar = 0
typeDim (TArr t _ _) = typeDim t + 1

typVars :: Typ -> Set Ident
typVars TStar = empty
typVars (TArr frm src tgt) = (typVars frm) `union` (expVars src) `union` (expVars tgt)

expVars :: Exp -> Set Ident
expVars (EVar id) = singleton id
expVars (ECoh id) = empty
expVars (EApp u v) = (expVars u) `union` (expVars v)

ctxtVars :: TCtxt -> Set Ident
ctxtVars (TNil id) = singleton id
ctxtVars (TCns tc (tId, _) (fId, _)) = insert tId (insert fId $ ctxtVars tc)
ctxtVars (TTgt tc) = ctxtVars tc
  
ctxtDim :: TCtxt -> Int
ctxtDim (TNil id) = 0
ctxtDim (TCns tc (tId, tFrm) (fId, fFrm)) = max (typeDim fFrm) (ctxtDim tc)
ctxtDim (TTgt tc) = ctxtDim tc  
  
--
-- I'm worried about what happens to the target marker here.
-- It looks to me like they all get preserved.  But this can't
-- be right, can it? 
--
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

target i (TCns tc (tId, tFrm) (fId, fFrm)) | i > typeDim tFrm = TCns (target i tc) (tId, tFrm) (fId, fFrm)
target i (TTgt tc) = TTgt (target i tc)

--
--  Typechecking Rules
--

checkDecls :: [Decl] -> TCM ()
checkDecls [] = return ()
checkDecls (d:ds) = do env <- checkDecl d
                       _ <- local (\_ -> env) (checkDecls ds)
                       return ()

checkDecl :: Decl -> TCM TCEnv
checkDecl (Coh id pms ty) =
  case pms of
    []                         -> throwError $ "Nothing to be done in empty context"
    (Tele x (TArr _ _ _)) : ps -> throwError $ "Context cannot start with an arrow"
    (Tele x TStar) : ps        -> do debug $ "========================="
                                     debug $ "Checking coherence: " ++ show id
                                     tctx <- checkTree (TNil x) ps 
                                     debug $ "Tree okay for " ++ show id
                                     debug $ "Result: " ++ show tctx

                                     (TCEnv gma rho) <- ask

                                     let ctxVars = ctxtVars tctx
                                         tyVars = typVars ty
                                         isAlgebraic = ctxVars `isSubsetOf` tyVars

                                     if (isAlgebraic)

                                       then do debug $ "Algebraic case"
                                               tyTm <- local (withTree tctx) (checkT ty)
                                               let cohTyTm = abstractTree tctx tyTm
                                                   cohD = eval cohTyTm rho

                                               debug $ "Finished: " ++ printTree id ++ " : " ++ show cohTyTm
                                               -- _ <- tcPrintDom cohD
                                               
                                               return $ TCEnv ((id,cohD):gma) (UpCoh rho id)

                                       else do debug $ "Src/Tgt check forced"
                                               (srcExp, srcFrm) <- tcExtSrc ty
                                               (tgtExp, tgtFrm) <- tcExtTgt ty

                                               let frmVars = typVars srcFrm -- or tgtFrm, they are the same
                                                   srcVars = frmVars `union` expVars srcExp
                                                   tgtVars = frmVars `union` expVars tgtExp
                                                   tctxDim = ctxtDim tctx
                                                   srcCtxt = source (tctxDim - 1) tctx
                                                   tgtCtxt = target (tctxDim - 1) tctx
                                               
                                               debug $ "Source context: " ++ show srcCtxt
                                               debug $ "Target context: " ++ show tgtCtxt

                                               _ <- verify (ctxtVars srcCtxt `isSubsetOf` srcVars) "Source is not algebraic"
                                               _ <- verify (ctxtVars tgtCtxt `isSubsetOf` tgtVars) "Target is not algebraic"

                                               (sFrmT, sExpT) <- local (withTree srcCtxt) $ do srcFrmT <- checkT srcFrm
                                                                                               srcFrmD <- tcEval srcFrmT
                                                                                               srcExpT <- check srcExp srcFrmD
                                                                                               return (srcFrmT, srcExpT)
                                               (tFrmT, tExpT) <- local (withTree tgtCtxt) $ do tgtFrmT <- checkT tgtFrm
                                                                                               tgtFrmD <- tcEval tgtFrmT
                                                                                               tgtExpT <- check tgtExp tgtFrmD
                                                                                               return (tgtFrmT, tgtExpT)
                                     
                                               let tyTm = Arr sFrmT sExpT tExpT
                                                   cohTyTm = abstractTree tctx tyTm
                                                   cohD = eval cohTyTm rho

                                               debug $ "Finished: " ++ printTree id ++ " : " ++ show cohTyTm
                                               -- _ <- tcPrintDom cohD

                                               return $ TCEnv ((id,cohD):gma) (UpCoh rho id)

  where verify b s = if b then return () else throwError s                                                   

checkDecl (Def id pms ty exp) = undefined 

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
                                                      

checkT :: Typ -> TCM Term
checkT t = case t of
  TStar            -> return Star
  TArr frm src tgt -> do frmT <- checkT frm
                         frmD <- tcEval frmT
                         srcT <- check src frmD
                         tgtT <- check tgt frmD
                         return $ Arr frmT srcT tgtT

check :: Exp -> D -> TCM Term
check e t = do --k <- tcDepth
               --debug $ "Checking " ++ printTree e ++ " has type " ++ show (rb t k)
               (eTm, eTy) <- checkI e
               k <- tcDepth
               let t0 = rb t k
                   t1 = rb eTy k
               if (t0 == t1) then return eTm
                 else throwError $ show t0 ++ " =/= " ++ show t1 ++ " while checking " ++ printTree e

checkI :: Exp -> TCM (Term, D)
checkI e = 
  case e of
    EVar id  -> do ty <- tcLookup id 
                   return (Var id, ty)
    ECoh id  -> do ty <- tcLookup id
                   --debug $ "Coherence lookup for " ++ printTree id ++ " gives:"
                   -- _ <- tcPrintDom ty
                   return (Cohr id, ty)
    EApp u v -> do --debug $ "Inferring type of " ++ printTree u
                   (uT, uTy) <- checkI u
                   -- _ <- tcPrintDom uTy
                   -- uD <- tcEval uT
                   (a, f) <- tcExtPi uTy
                   vT <- check v a
                   vD <- tcEval vT
                   let rTy = f vD
                   -- debug $ "After evaluation, we have: "
                   -- _ <- tcPrintDom rTy
                   return (App uT vT, rTy)
                   

debug :: String -> TCM ()
debug msg = liftIO $ putStrLn msg
