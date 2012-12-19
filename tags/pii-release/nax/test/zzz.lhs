\documentclass{article}

%include polycode.fmt
%include lhs2TeX.fmt
%include agda.fmt

%format with = "\textbf{with}\,"
%format where = "\;\textbf{where}"
%format fixpoint = "\,\textbf{fixpoint}"

%format In (a) = "\mathsf{In}^{" a "}"
%format . = "\mathbin{.}"

%format mcata (a) = "\mathsf{MIt}" "^{" a "}"

\begin{document}

\begin{code}
instance Ord Int where a > b = a > b


data Tag = E | O

flip E = O
flip O = E
    
data P : (Tag -> Nat -> *) -> Tag -> Nat -> * where
  Base : P r {E} {In [*] Zero} 
  StepO : r {O} {i} -> P r {E} {`succ i}
  StepE : r {E} {i} -> P r {O} {`succ i}
    deriving fixpoint Proof
    
flop x = 
   mcata {{t} {i} . Proof {`flip t} {`succ i}} x    
     with  f Base = stepE base
           f (StepO p) = stepE(f p)
           f (StepE p) = stepO(f p)    
\end{code}


\end{document}
