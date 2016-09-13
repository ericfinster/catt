--
--  TypeChecker.hs - Catt Typechecker
--

module TypeChecker where

import Control.Monad.Except
import Control.Monad.Reader

import Syntax.AbsCatt
import Syntax.PrintCatt

--
-- Tree Contexts
--

data Gma = Gma [(Ident, Typ)] Typ

--
--  Typechecking Environment
--

data TCEnv = TCEnv
  { envContext :: Gma
  }

--
--  Typechecking Monad
--

type TCM = ReaderT TCEnv (ExceptT String IO)

tcLookup :: Ident -> TCM Typ
tcLookup id = do
  (Gma tys _) <- reader envContext
  case lookup id tys of
    Nothing -> throwError $ "Lookup failed for id: " ++ show id
    Just ty -> return ty
  
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
checkDecl (Coh id pms ty) = undefined
checkDecl (Def id pms ty exp) = return ()

-- checkTree :: [Tele] -> TCM Gma
-- checkTree [] = throwError "Nothing to do in an empty context"
-- checkTree [Tele _ (TArr  _ _)] = throwError "Initial assumption cannot be an arrow!"
-- checkTree [Tele id TStar] = return $ Gma [(id, TStar)] TStar
-- checkTree ((Tele f ftyp):(Tele t ttyp):ts) = undefined

checkCoherence :: Ident -> [Tele] -> Typ -> TCM ()
checkCoherence id pms ty = undefined

checkT :: Typ -> TCM ()
checkT TStar = return ()
-- checkT (TArr a b) = do
--   at <- checkI a
--   bt <- checkI b
--   if (at == bt)
--     then return ()
--     else throwError $
--          "Typing mismatch:\n" ++
--          printTree a ++ " : " ++ printTree at ++ "\n" ++
--          printTree b ++ " : " ++ printTree bt 
  
check :: Exp -> Typ -> TCM ()
check e t = undefined

checkI :: Exp -> TCM Typ
checkI e =
  case e of
    EVar id -> tcLookup id
    _ -> throwError "Unimplemented"
    
