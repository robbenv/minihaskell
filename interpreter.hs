-- name: CHEN LUWEI
-- id: 2110112
-- acknowledgements: Li Ruizhi

import TRS
import Parser
import System.Environment 

data MarkedTerm = MApp MarkedTerm MarkedTerm | MCon String | NF Term

substitute :: Term -> Substitution -> Term
substitute (Var x) sigma
  | Just t <- lookup x sigma = t 
  | otherwise                = Var x　
substitute (Con f) sigma = Con f
substitute (App t1 t2) sigma = App (substitute t1 sigma) (substitute t2 sigma) 

match :: Term -> Term -> Maybe Substitution
match s t = match' [] [(s, t)] 


match' :: Substitution -> [(Term, Term)] -> Maybe Substitution
match' sigma [] = Just sigma 
match' sigma ((App (Con f) x, App (Con g) t) : ps) 
  | f == g = match' sigma ((x, t) : ps) 
match' sigma (((Con a), (Con b)) : ps) 
   | a == b = match' ((a, (Con b)) : sigma) ps 
match' sigma ((App x1 x2, App t1 t2) : ps) = match' sigma ((x1, t1) : (x2, t2) :ps) 
match' sigma ((Var x, t) : ps) 
  | Just t' <- lookup x sigma, t == t' =
      match' sigma ps 
  | Nothing <- lookup x sigma =
      match' ((x, t) : sigma) ps
match' _ _ = Nothing 


rewriteAtRoot :: TRS -> Term -> Maybe Term
rewriteAtRoot [] t = Nothing 
rewriteAtRoot ((l, r) : rules)  t | Just sigma <- (match l t) = Just (substitute r sigma)  
                                  | Nothing <- (match l t) = (rewriteAtRoot rules t) 


rewrite :: TRS -> Term -> Maybe Term
rewrite r (Var x) = rewriteAtRoot r (Var x)
rewrite r (Con a) = rewriteAtRoot r (Con a)
rewrite r (App t1 t2) = case (rewrite r t1) of 
                          Just u1 -> Just (App u1 t2)
                          Nothing -> case (rewrite r t2) of
                                      Just u2 -> Just (App t1 u2)
                                      Nothing -> case rewriteAtRoot r (App t1 t2) of
                                                  Just uapp -> Just uapp
                                                  Nothing -> Nothing

nf1 :: TRS -> Term -> Term
nf1 r t | (Just u) <- (rewrite r t) = (nf1 r u)
        | Nothing <- (rewrite r t) = t

---------------------------------------------

substitute2 :: Term -> Substitution -> MarkedTerm
substitute2 (Var x) sigma
  | Just t <- lookup x sigma = NF t
  | otherwise                =  MCon x
substitute2 (Con f) sigma = MCon f
substitute2 (App t1 t2) sigma = MApp (substitute2 t1 sigma) (substitute2 t2 sigma) 

rewriteAtRoot2 :: TRS -> Term -> MarkedTerm 
rewriteAtRoot2 [] t = NF t
rewriteAtRoot2 ((l, r) : rules)  t | Just sigma <- (match l t) = substitute2 r sigma  
                                  | Nothing <- (match l t) = (rewriteAtRoot2 rules t) 

rewrite2 :: TRS -> MarkedTerm -> MarkedTerm
rewrite2 r (MCon ma) = rewriteAtRoot2 r (Con ma)
rewrite2 r (NF t) = NF t
rewrite2 r (MApp mt1 mt2) = case (rewrite2 r mt1) of 
                              NF nfu1 ->  case (rewrite2 r mt2) of                                  
                                            NF nfu2 -> rewriteAtRoot2 r (App nfu1 nfu2)
                                            mu2 -> (MApp (NF nfu1) mu2)
                              mu1 -> (MApp mu1 mt2) 


nf2 :: TRS -> MarkedTerm -> Term
nf2 r mt | (NF nu) <- (rewrite2 r mt) = nu 
         | mu <- (rewrite2 r mt) = (nf2 r mu)     


nf3 :: TRS -> MarkedTerm -> Term
nf3 r (MCon mt) | (NF nu) <- (rewrite2 r (MCon mt)) = nu
               | mu <- (rewrite2 r (MCon mt)) = nf3 r mu
nf3 r (MApp mt1 mt2) | (NF nu)  <- (rewrite2 r nf') = nu
                       | mu <- (rewrite2 r nf') = nf3 r mu
      where nf' = case  (MApp mt1 mt2) of
                   (MApp (NF nt1) (NF nt2)) ->  (MApp (NF nt1) (NF nt2))
                   (MApp (NF nt1) mt2) -> (MApp (NF nt1) (NF (nf3 r mt2)))
                   (MApp mt1 (NF nt2)) -> (MApp (NF (nf3 r mt1)) (NF nt2))
                   otherwise -> (MApp (NF (nf3 r mt1)) (NF (nf3 r mt2)))


main :: IO ()
main = do
  file : _ <- getArgs
  result <- readTRSFile file
  case result of
    Left e    -> print e
    Right trs -> do       
     --putStrLn (show (nf1 trs (Con "main")))
    --putStrLn (show (nf2 trs (MCon "main")))                                 
    putStrLn (show (nf3 trs (MCon "main")))

