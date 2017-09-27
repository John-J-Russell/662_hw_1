module Core where

--------------------------------------------------------------------------------
-- Core syntax
--------------------------------------------------------------------------------

type Ident = String
data Core = CInt Integer | CAdd Core Core | CMult Core Core
          | CBool Bool | CIs0 Core | CIf Core Core Core
          | CVar Ident | CLam Ident CType Core | CApp Core Core
          | CPair Core Core | CLetPair Ident Ident Core Core
          | CInl CType CType Core | CInr CType CType Core
          | CCase Core (Ident, Core) (Ident, Core)
  deriving (Eq, Show)

data CType = CTInt | CTBool | CTFun CType CType
           | CTPair CType CType | CTSum CType CType
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Typing and type checking
--------------------------------------------------------------------------------

type TEnv = [(Ident, CType)]

check :: TEnv -> Core -> Maybe CType
check _ (CInt _) =
    return CTInt
check g (CAdd e1 e2) =
    do CTInt <- check g e1
       CTInt <- check g e2
       return CTInt
check g (CMult e1 e2) =
    do CTInt <- check g e1
       CTInt <- check g e2
       return CTInt
check _ (CBool _) =
    return CTBool
check g (CIs0 e) =
    do CTInt <- check g e
       return CTBool
check g (CIf e1 e2 e3) =
    do CTBool <- check g e1
       t2 <- check g e2
       t3 <- check g e3
       if t2 == t3 then return t2 else Nothing
check g (CVar x) =
    lookup x g
check g (CLam x t1 e) =
    do t2 <- check ((x, t1):g) e
       return (CTFun t1 t2)
check g (CApp e1 e2) =
    do CTFun t1 t2 <- check g e1
       t1' <- check g e2
       if t1 == t1' then return t2 else Nothing
check g (CPair e1 e2) =
    do t1 <- check g e1
       t2 <- check g e2
       return (CTPair t1 t2)
check g (CLetPair x1 x2 e1 e2) =
    do CTPair t1 t2 <- check g e1
       check ((x1, t1) : (x2, t2) : g) e2
check g (CInl t1 t2 e) =
    do x1 <- check g e
       if t1 == x1 then Just (CTSum t1 t2) else Nothing 
--error "Type checking for Inl not implemented"
check g (CInr t1 t2 e) =
    do x <- check g e
       if x == t2 then Just (CTSum t1 t2) else Nothing
--    error "Type checking for Inr not implemented"
check g (CCase e (x1, e1) (x2, e2)) =
    error "Type checking for case is not implemented"

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

data Value = VInt Integer | VBool Bool | VFun VEnv Ident Core | VPair Value Value
           | VInl Value | VInr Value
  deriving (Eq, Show)

type VEnv = [(Ident, Value)]

eval :: VEnv -> Core -> Value
eval _ (CInt x) =
    VInt x
eval h (CAdd e1 e2) =
    let VInt x1 = eval h e1
        VInt x2 = eval h e2 in
    VInt (x1 + x2)
eval h (CMult e1 e2) =
    let VInt x1 = eval h e1
        VInt x2 = eval h e2 in
    VInt (x1 * x2)
eval _ (CBool b) =
    VBool b
eval h (CIs0 e) =
    let VInt x = eval h e in
    VBool (x == 0)
eval h (CIf e1 e2 e3) =
    let VBool b = eval h e1 in
    if b then eval h e2 else eval h e3
eval h (CVar x) =
    let Just v = lookup x h in v
eval h (CLam x _ e) =
    VFun h x e
eval h (CApp e1 e2) =
    let VFun h' x e = eval h e1
        v = eval h e2 in
    eval ((x, v) : h') e
eval h (CPair e1 e2) =
    let v1 = eval h e1
        v2 = eval h e2 in
    VPair v1 v2
eval h (CLetPair x1 x2 e1 e2) =
    let VPair v1 v2 = eval h e1 in
    eval ((x1, v1) : (x2, v2) : h) e2
eval h (CInl _ _ e) =
    error "Evaluation for Inl not implemented"
eval h (CInr _ _ e) =
    error "Evaluation for Inr not implemented"
eval h (CCase e (x1, e1) (x2, e2)) =
    error "Evaluation for case not implemented"
