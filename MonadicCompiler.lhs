G52AFP Coursework 2 - Monadic Compiler

Godly Obeng Karikari
psygo1@nottingham.ac.uk


> import Control.Monad.Trans.Writer.Lazy
> import Control.Monad.Trans.Class

--------------------------------------------------------------------------------

Imperative language:

> data Prog = Assign Name Expr
>           | If Expr Prog Prog
>           | While Expr Prog
>           | Seqn [Prog]
>             deriving Show
>
> data Expr = Val Int | Var Name | App Op Expr Expr
>             deriving Show
>
> type Name = Char
>
> data Op   = Add | Sub | Mul | Div
>             deriving Show

Factorial example:

> fac :: Int -> Prog
> fac n = Seqn [Assign 'A' (Val 1),
>               Assign 'B' (Val n),
>               While (Var 'B') (Seqn
>                  [Assign 'A' (App Mul (Var 'A') (Var 'B')),
>                   Assign 'B' (App Sub (Var 'B') (Val (1)))])]

Virtual machine:

> type Stack = [Int]
>
> type Mem   = [(Name,Int)]
>
> type Code  = [Inst]
> 
> data Inst  = PUSH Int
>            | PUSHV Name
>            | POP Name
>            | DO Op
>            | JUMP Label
>            | JUMPZ Label
>            | LABEL Label
>              deriving Show
> 
> type Label = Int

State monad:

> type State = Label
>
> newtype ST a = S (State -> (a, State))
>
> app :: ST a -> State -> (a,State)
> app (S st) x 	=  st x
>
> instance Functor ST where
>    -- fmap :: (a -> b) -> ST a -> ST b
>    fmap g st = S (\s -> let (x,s') = app st s in (g x, s'))
>
> instance Applicative ST where
>    -- pure :: a -> ST a
>    pure x = S (\s -> (x,s))
>
>    -- (<*>) :: ST (a -> b) -> ST a -> ST b
>    stf <*> stx = S (\s ->
>       let (f,s')  = app stf s
>           (x,s'') = app stx s' in (f x, s''))
>
> instance Monad ST where
>    -- return :: a -> ST a
>    return x = S (\s -> (x,s))
>
>    -- (>>=) :: ST a -> (a -> ST b) -> ST b
>    st >>= f = S (\s -> let (x,s') = app st s in app (f x) s')

--------------------------------------------------------------------------------

This is the program counter (ProgC)

> type ProgC = Int

This helper function changes expression into code

> compExpr :: Expr -> Code
> compExpr (Val n) = [PUSH n]
> compExpr (Var x) = [PUSHV x]
> compExpr (App o exp1 exp2) = (compExpr exp1) ++ (compExpr exp2) ++ [DO o]


This is also another helper function used to increment the label

> fresh :: ST Label
> fresh = S (\n -> (n, n + 1))


This helper function changes the statements (Assign, If, While, Seqn)
into what can be understood by the machine code. I have also used Writer T
to combine the Writer Monad and the state monad.

> compProg :: Prog -> WriterT Code ST ()
> compProg (Assign n e) = do tell (compExpr e)
>                            tell [POP n]
> compProg (If e l r)   = do n1 <- lift fresh
>                            n2 <- lift fresh
>                            tell (compExpr e)
>                            tell [JUMPZ n1]
>                            compProg l
>                            tell [JUMP n2]
>                            tell [LABEL n1]
>                            compProg r
>                            tell [LABEL n2]
> compProg (While e p)  = do n1 <- lift fresh
>                            n2 <- lift fresh
>                            tell [LABEL n1]
>                            tell (compExpr e)
>                            tell [JUMPZ n2]
>                            compProg p
>                            tell [JUMP n1]
>                            tell [LABEL n2]
> compProg (Seqn [])      = do tell []
> compProg (Seqn (p:ps))  = do compProg p
>                              compProg (Seqn ps)



This is the main function which combines all the helper functions
to get the corresponding machine code.

> comp :: Prog -> Code
> comp p = fst (app(execWriterT (compProg p)) 0)


This function gives the implementations of Add, Sub, Mul, Div since they
are just declared but not implemented

> calc :: Op -> Int -> Int -> Int
> calc Add l r = l + r
> calc Sub l r = l - r
> calc Mul l r = l * r
> calc Div l r = l `div` r


This helper function searches for a corresponding int value
which matches the Name and Mem input

> nMem :: Name -> Mem -> Maybe Int
> nMem x [] = Nothing
> nMem x (m:ms) | x == fst m = Just (snd m)
>               | otherwise  = nMem x ms


This function uses the nMem function to update the stack by
putting the value at the top.

> memN :: (Mem, Stack) -> Name -> Stack
> memN (m, s) n = x:s where Just x = nMem n m


This function is used to update the value in memory

> update :: (Name, Int) -> Mem -> Mem
> update (n, i) m | nMem n m == Nothing = m ++ [(n, i)]
>                 | otherwise = takeWhile (\a -> fst a /= n) m ++ 
>                               [(n, i)] ++ 
>                               tail (dropWhile (\a -> fst a /= n) m)


This function searches a lable's position in the code and return the location

> cLabel :: Code -> Label -> ProgC
> cLabel ((LABEL x):xs) l | x == l = 0
> cLabel (x:xs) l = 1 + (cLabel xs l)



> insExec :: (Code, ProgC, Mem, Stack) -> Inst -> (Code, ProgC, Mem, Stack)
> insExec (c, p, m, s) (PUSH i)     = (c, p+1, m, i:s)
> insExec (c, p, m, s) (PUSHV n)    = (c, p+1, m, memN (m, s) n)
> insExec (c, p, m, x:xs) (POP n)   = (c, p+1, update (n, x) m, xs)
> insExec (c, p, m, x:y:zs) (DO o)  = (c, p+1, m, (calc o y x) : zs)
> insExec (c, p, m, s) (JUMP l)     = (c, cLabel c l, m, s)
> insExec (c, p, m, x:xs) (JUMPZ l) | x == 0 = (c, cLabel c l, m, xs) 
>                                | otherwise = (c, p+1, m, xs)
> insExec (c, p, m, s) (LABEL l)    = (c, p+1, m, s)



> exec' :: (Code, ProgC, Mem, Stack) -> (Code, ProgC, Mem, Stack)
> exec' (c, p, m, s) | p < (length c) = exec' (insExec (c, p, m, s) (c !! p))
>                    | otherwise      = (c, p, m, s)



This function takes a code snippet, and return the final content in memory.

> exec :: Code -> Mem
> exec c = m where (c', p, m, s) = exec' (c, 0, [], [])