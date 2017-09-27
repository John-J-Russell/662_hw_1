module Simple where

import Control.Monad (guard)
import Text.Parsec hiding (parse)
import Text.Parsec.Language
import Text.Parsec.Token as T

import Core

--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

parse :: String -> Either ParseError Core
parse = runParser (whiteSpace l >> terminal exprp) () ""
    where l = makeTokenParser $
              haskellDef { commentLine = "--"
                         , reservedNames = ["True", "False", "if", "then", "else",
                                            "let", "in", "Int", "Bool",
                                            "Inl", "Inr", "case", "of"]
                         , reservedOpNames = ["+", "*", "\\", "->", ":", ","] }

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

          exprp = lamp

          lamp = (do reservedOp "\\"
                     x <- identifier
                     reservedOp ":"
                     t <- addtyp
                     reservedOp "->"
                     e <- exprp
                     return (CLam x t e)) <|>
                 (do reserved "let"
                     reservedOp "("
                     x1 <- identifier
                     reservedOp ","
                     x2 <- identifier
                     reservedOp ")"
                     reservedOp "="
                     e1 <- exprp
                     reserved "in"
                     e2 <- exprp
                     return (CLetPair x1 x2 e1 e2)) <|>
                 (do reserved "if"
                     e1 <- exprp
                     reserved "then"
                     e2 <- exprp
                     reserved "else"
                     e3 <- exprp
                     return (CIf e1 e2 e3)) <|>
                 (do reserved "case"
                     e <- exprp
                     reserved "of"
                     reserved "Inl"
                     x1 <- identifier
                     reservedOp "->"
                     e1 <- exprp
                     reservedOp "|"
                     reserved "Inr"
                     x2 <- identifier
                     reservedOp "->"
                     e2 <- exprp
                     return (CCase e (x1, e1) (x2, e2))) <|>
                 addp

          addp = chainl1 multp (reservedOp "+" >> return CAdd)

          multp = chainl1 applp (reservedOp "*" >> return CMult)

          applp = do es <- many1 atomp
                     case es of
                       [CVar "isz", e] -> return (CIs0 e)
                       _ -> return (foldl1 CApp es)

          atomp = choice [ CInt `fmap` lexeme intConst
                         , CBool `fmap` boolConst
                         , CVar `fmap` identifier
                         , do ctor <- (reserved "Inl" >> return CInl) <|>
                                      (reserved "Inr" >> return CInr)
                              (t1, t2) <- brackets (do t1 <- multyp
                                                       reservedOp "+"
                                                       t2 <- multyp
                                                       return (t1, t2))
                              e <- exprp
                              return (ctor t1 t2 e)
                         , do es <- parens (sepBy1 exprp comma)
                              case es of
                                [e] -> return e
                                [e1, e2] -> return (CPair e1 e2)
                                _ -> fail "Tuple too big (or small)" ]

          intConst = do ds <- many1 digit
                        return (read ds)

          boolConst = (reserved "True" >> return True) <|>
                      (reserved "False" >> return False)

          typep = chainr1 addtyp (reservedOp "->" >> return CTFun)

          addtyp = chainl1 multyp (reservedOp "+" >> return CTSum)

          multyp = chainl1 atomtp (reservedOp "*" >> return CTPair)

          atomtp = (reserved "Int" >> return CTInt) <|>
                   (reserved "Bool" >> return CTBool) <|>
                   parens typep
