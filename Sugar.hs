module Sugar where

import Control.Monad (guard)
import Data.Char (isLower, isUpper)
import Data.List (sortBy)
import Text.Parsec hiding (parse)
import Text.Parsec.Language
import Text.Parsec.Token as T

import Core
import Data.Maybe
--------------------------------------------------------------------------------
-- Sugared syntax
--------------------------------------------------------------------------------

data Type = TInt | TBool | TFun Type Type
          | TDatatype String
  deriving (Eq, Show)

data Expr = EInt Integer | EAdd Expr Expr | EMult Expr Expr
          | EBool Bool | EIs0 Expr | EIf Expr Expr Expr
          | EVar Ident | ELam Ident Type Expr | EApp Expr Expr
          | ECon Ident [Expr] | ECase Expr [(Ident, [Ident], Expr)]
          | EDatatype Ident [(Ident, [Type])] Expr
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Desugaring
--------------------------------------------------------------------------------

type DtypeEnv = [(Ident, [(Ident, [CType])])]

desugarTy :: DtypeEnv -> Type -> Maybe CType
desugarTy _ TInt =
    return CTInt
desugarTy _ TBool =
    return CTBool
desugarTy dtypes (TFun t1 t2) =
    do t1' <- desugarTy dtypes t1
       t2' <- desugarTy dtypes t2
       return (CTFun t1' t2')

-- Takes a T we produce in the other desugar EDatatype, gives a CSum of
-- CProducts
-- k is a couplet, second element has the goods
-- in each pair in the list, the second element is also a list that needsw to
-- be parsed into a pair/product thing "CTPair CType CType"
-- These need to be summed together in "CTSum CType CType"
desugarTy dtypes (TDatatype k) = --k is constructor ?
    Just(outerProcessing (fromJust(lookup k dtypes)))

desugar :: DtypeEnv -> Expr -> Maybe Core
desugar _ (EInt i) =
    return (CInt i)
desugar dtypes (EAdd e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (CAdd e1' e2')
desugar dtypes (EMult e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (CMult e1' e2')
desugar _ (EBool b) =
    return (CBool b)
desugar dtypes (EIs0 e) =
    do e' <- desugar dtypes e
       return (CIs0 e')
desugar dtypes (EIf e1 e2 e3) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       e3' <- desugar dtypes e3
       return (CIf e1' e2' e3')
desugar _ (EVar x) =
    return (CVar x)
desugar dtypes (ELam x t e) =
    do t' <- desugarTy dtypes t
       e' <- desugar dtypes e
       return (CLam x t' e')
desugar dtypes (EApp e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (CApp e1' e2')
desugar dtypes (EDatatype dtname ctors e) = -- name, constructors, body makes and extends environment ctors is a list
    desugar ( (dtname , (outerListProcess dtypes ctors)) : dtypes) e 
desugar dtypes (ECon k es) =
    Just(outerConsProcessing dtypes dtypes k es)
desugar dtypes (ECase e bs) = 
    CCase (desugar dtypes e) {-desugar left case-} {-desugar right cases-}
--  (JUST?) CCase Core (Ident, Core) (Ident, Core)
--    error "Desugaring for cases not implemented"

--e will be variable, and bs are cases
--bs is of format [(Ident, [Ident], Expr)]
--Remember: we only need to desugar it, not solve it.

--Turn a list of EInts or similar into pairs of CInts or similar
fancify dtype [e] =
    fromJust(desugar dtype e)
fancify dtype (e:es) =
    CPair (fromJust(desugar dtype e)) (fancify dtype es)
injectorBuild dtype [(kname, thetypes)] k es=
    if (k == kname) 
       then{- (innerProcessing thetypes)-} (fancify dtype es) 
       else error "I don't even know"
injectorBuild dtype ((kname , thetypes ) : rest) k es =
    if (k == kname) 
       then CInl (innerProcessing thetypes) (outerProcessing rest) (fancify dtype es) 
       else CInr (innerProcessing thetypes) (outerProcessing rest) (injectorBuild dtype rest k es)
outerConsProcessing fulldtype [dtype] k es =
    if (lookup k (snd dtype)) == Nothing then error "Does not exist" else injectorBuild fulldtype (snd dtype) k es
outerConsProcessing fulldtype (dtypehead : dtyperest) k es =
    if (lookup k (snd dtypehead)) == Nothing then outerConsProcessing fulldtype dtyperest k es else injectorBuild fulldtype (snd dtypehead) k es



--For desugar EDatatype dtname
innerListProcess dtypes [x] =
    [fromJust(desugarTy dtypes x)]
innerListProcess dtypes (x : xs) =
    fromJust((desugarTy dtypes x)) : (innerListProcess dtypes xs)
outerListProcess dtypes [(varname, typelist)] =
    [(varname , innerListProcess dtypes typelist)]
outerListProcess dtypes ( (varname , typelist) : rest) =
    ( varname , (innerListProcess dtypes typelist) ) : (outerListProcess dtypes rest)


--For desugarTY TDatatypes
innerProcessing [x] =
    x
innerProcessing ( x : xs) =
    CTPair x (innerProcessing xs)
outerProcessing [(varname , varlist)] =
    innerProcessing varlist
outerProcessing ((varname , varlist) : therest) =
    CTSum (innerProcessing varlist) (outerProcessing therest)
--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

parse :: String -> Either ParseError Expr
parse = runParser (terminal (whiteSpace l >> exprp)) () ""
    where l = makeTokenParser $
              haskellDef { commentLine = "--"
                         , reservedNames = ["True", "False", "if", "then", "else",
                                            "let", "in", "Int", "Bool",
                                            "case", "of", "data"]
                         , reservedOpNames = ["+", "*", "\\", "->", ":", ",", ";", "|"] }

          terminal p = do x <- p
                          eof
                          return x
          identifier = T.identifier l
          reserved = T.reserved l
          reservedOp = T.reservedOp l
          parens = T.parens l
          brackets = T.brackets l
          lexeme = T.lexeme l
          comma = T.comma l

          variable = try (do v <- identifier
                             guard (isLower (head v))
                             return v) <?> "identifier"

          constructor = try (do v <- identifier
                                guard (isUpper (head v))
                                return v) <?> "constructor"

          exprp = lamp

          lamp = (do reservedOp "\\"
                     x <- identifier
                     reservedOp ":"
                     t <- atomtp
                     reservedOp "->"
                     e <- exprp
                     return (ELam x t e)) <|>
                 (do reserved "if"
                     e1 <- exprp
                     reserved "then"
                     e2 <- exprp
                     reserved "else"
                     e3 <- exprp
                     return (EIf e1 e2 e3)) <|>
                 (do reserved "data"
                     k <- constructor
                     reservedOp "="
                     ctors <- sepBy1 (do k <- constructor
                                         vs <- many typep
                                         return (k, vs))
                                     (reservedOp "|")
                     reserved "in"
                     e <- exprp
                     return (EDatatype k ctors e)) <|>
                 (do reserved "case"
                     e <- exprp
                     reserved "of"
                     bs <- sepBy1 (do k <- constructor
                                      vs <- many variable
                                      reservedOp "->"
                                      e <- exprp
                                      return (k, vs, e))
                                  (reservedOp "|")
                     return (ECase e bs)) <|>
                 addp

          addp = chainl1 multp (reservedOp "+" >> return EAdd)

          multp = chainl1 applp (reservedOp "*" >> return EMult)

          applp = (do k <- constructor
                      es <- many atomp
                      return (ECon k es)) <|>
                  (do es <- many1 atomp
                      case es of
                        [EVar "isz", e] -> return (EIs0 e)
                        _ -> return (foldl1 EApp es))

          atomp = choice [ EInt `fmap` lexeme intConst
                         , EBool `fmap` boolConst
                         , EVar `fmap` identifier
                         , parens exprp ]

          intConst = do ds <- many1 digit
                        return (read ds)

          boolConst = (reserved "True" >> return True) <|>
                      (reserved "False" >> return False)

          typep = chainr1 atomtp (reservedOp "->" >> return TFun)

          atomtp = (reserved "Int" >> return TInt) <|>
                   (reserved "Bool" >> return TBool) <|>
                   (TDatatype `fmap` constructor) <|>
                   parens typep
