\documentclass[11pt, a4paper, oneside]{amsart}

\title{The Pigeonhole Principle}
\date{Last updated : \today}
\author{Jonathan Prieto-Cubides}

\input{macros.tex}
\usepackage{latex/agda}

\begin{document}

\maketitle

\begin{abstract}
There are many formulations of the so-called Pigeonhole principle,
some of them proved in constructive mathematics and formalized
in some proof-assistants. In this work, we show one these formulations
proved in the context of Univalent Type theory and
formalized in the proof-assistant Agda.
\end{abstract}

\section{Introduction}

The pigeonhole principle says that \emph{if you put $n$ pigeons in
$m$ holes, with $m < n$, then at least one hole has more
than one pigeon in it.
}\\

In~\cite{symmetrybook} the authors give the following formulation
(\Cref{lem:PHP}) of the Pigeonhole Principle joint with a constructive proof
that it holds. The proof can be found formalized in \texttt{Coq}\footnote{In
the \texttt{Coq} standard library
\url{https://coq.inria.fr/library/Coq.Sets.Image.html}.}.

\begin{theorem}[Lemma 2.15.6 in \cite{symmetrybook}]\label{lem:PHP}
For all $N:ℕ$ and $f:ℕ\to ℕ$ such that $f(n)<N$
for all $n<N+1$, there exist $m < n < N+1$ such that $f(n)=f(m)$.
\end{theorem}
The function $f$ above intends to maps the number of a pigeon in $\{0\cdots n−1\}$ to
the number of its hole in $\{0\cdots m−1\}$.

In this work, we consider an equivalent formulation in \Cref{pigeon-theorem},
which can be seen as a generalization of \Cref{lem:PHP}. The formal statement
says, there is no injective function that can go from a finite set to a smaller
one. We denote the finite set of $n$ elements with $[n]$.

\begin{theorem}[Pigeonhole Theorem]\label{pigeon-theorem}
For any $n,\, m : ℕ$ when $m < n$,  a function $f : [ n ] \to [ m ]$
can not be injective.
\end{theorem}

Another similar formulation can be stated when instead of finite sets, we
consider for any function, the cardinality of its domain and its image. We
give the following formulations that follow the same fashion of
\Cref{pigeon-theorem}.

For any $n : ℕ$, $f : [n] \to [n]$.
\begin{itemize}
\item If $f$ is a surjective, then $f$ is injective, and
\item If $f$ is injective, then $f$ is surjective.
\end{itemize}

\section{Notation}

\subsection{Agda formalization}

To check the proof in~\Cref{proof-pigeon-theorem} of \Cref{pigeon-theorem}, we
use \texttt{Agda v2.6.0} without the \emph{Axiom K} to be consistent with
Univalent mathematics. We also import a library to work with Homotopy Type
Theory called \texttt{MiniHoTT}\footnote{Available on
\url{http://jonaprieto.github.io/mini-hott}.} that includes some type
definitions and theorems we need.

\begin{code}
{-# OPTIONS --without-K  #-}
open import MiniHoTT
\end{code}

\begin{code}[hide]
  hiding (Fin)
module _ {ℓ : Level} where
  open ℕ-ordering ℓ
  ⟦_⟧ = ⟦_⟧₂ {ℓ}
\end{code}

\subsection{Types}

We assume the reader is familiar with type theory notation as in Book HoTT
\cite{hottbook} and with the basic \Agda\, syntax. For any type $A : \Type$,
we define in~\Cref{eq:minus} the type $A - \{x\}$ as the type\footnote{We
denote this symbol, minus, as  double-back-slashes in \Agda.} of elements of
which are different with $x$. We will use this type to talk about the finite
set $[n]$ without a point $x$, i.e., $[n] - \{ x\}$. The finite set of $n$
elements in \texttt{Agda} is denoted by \texttt{⟦ n ⟧}. We are using for
finite sets the definition that says $[n + 1] :\equiv 𝟙 + [n]$ and $[0]
:\equiv 𝟘$. Propositional equality is denoted by ($\equiv$) instead of $(=)$.
The type $ℕ$ for natural numbers has two constructors \texttt{zero}, and
\texttt{succ}. The coproduct of types $A$ and $B$ is denoted by $A+B$ and it
has two introduction rules named \texttt{inr}, and \texttt{inl}. We use the
direct composition of functions also called \emph{diagramatic} composition,
denoted in \texttt{Agda} by (\texttt{f :> g}) for $f : A \to B$ and $g : B \to
C$, for types $A,B,$ and $C$.

\begin{equation}\label{eq:minus}
A - \{x\} :\equiv \sum_{a : A} \, (a ≡ x) → \bot.
\end{equation}

\begin{code}[hide]
  _─_  : ∀ {ℓ : Level} → (A : Type ℓ) (x : A) → Type ℓ
  _─_  {ℓ} A x  = ∑ A (λ a → ((a ≡ x) → ⊥ ℓ))
\end{code}

\section{A proof of \Cref{pigeon-theorem}}

We first need to show there exists an equivalence between two (finite) types
that differs only by one point. So we define the following (recursive)
functions \texttt{e→} and \texttt{e←}.

\begin{figure}
\includegraphics[width=0.9\textwidth]{removing-one-point-from-finite-set.pdf}
\caption{Construction of the equivalence $e$ in (\Cref{equivalence-e}).
The directions of the arrows (forward and backward) correspond to the functions
in \Cref{definition-e-fun} and \Cref{definition-e-inv}, respectively.}
\end{figure}

\begin{definition}\label{definition-e-fun}
\hspace{5cm}
 \begin{code}
  e→ : ∀ (n : ℕ) → (x : ⟦ succ n ⟧)
     --------------------------
     → ⟦ n ⟧ → ⟦ succ n ⟧ ─ x
\end{code}

\begin{code}
  e→ (succ n) (inl x) y = inr y , λ ()
  e→ (succ n) (inr x) (inl y) = inl _ , λ ()
  e→ (succ n) (inr x) (inr y)
    = (inr (π₁ $ e→ n x y)) , λ p → π₂ (e→ n x y) (inr-is-injective p)
\end{code}
\end{definition}

\begin{definition}\label{definition-e-inv}
\hspace{5cm}
\begin{code}
  e← : ∀ (n : ℕ) → (x : ⟦ succ n ⟧)
      --------------------------
     → (⟦ succ n ⟧ ─ x) → ⟦ n ⟧
\end{code}

\begin{code}
  e← 0 (inl ∗) (inl ∗ , b) = b (ap inl idp)
  e← (succ n) (inl x) (inl x₁ , b) = inl _
  e← n (inl x) (inr y , b)  = y
  e← (succ 0) (inr x) (inl x₁ , π₄) = x
  e← (succ (succ n)) (inr x) (inl x₁ , π₄) = inl ∗
  e← (succ n) (inr x) (inr y , π₄)
    = inr (e← n x (y , (π₄ ∘  (ap inr ))))
\end{code}

\begin{code}[hide]
  DEF-g : ∀ {n}{x}{y}{π₄}
      → e← (succ n) (inr x) (inr y , π₄)
      ≡ inr (e← n x (y , (π₄ ∘  (ap (inr {A = 𝟙 ℓ}{𝟙 ℓ + ⟦ n ⟧}) ))))

  DEF-g {0} {inl ∗} {inl ∗} {π₄} = idp
  DEF-g {succ n} {inl ∗} {inl ∗} {π₄} = idp
  DEF-g {succ n} {inl x} {inr x₁} {π₄} = idp
  DEF-g {succ n} {inr x} {inl x₁} {π₄} = idp
  DEF-g {succ n} {inr x} {inr x₁} {π₄} = idp
\end{code}

\end{definition}
gm
\begin{lemma}\label{equivalence-e}
For any $n : ℕ$ , $x : [ n + 1 ]$,
the types $[n]$ and $[ n + 1] - \{x\}$ are (homotopy) equivalent.
We shall denote this equivalence as $e(n,x)$.
\end{lemma}

\begin{proof}[Sketch of the Proof.]
We can show that the equivalence follows by showing  \texttt{e→} has as inverse
the function \texttt{e←}. The corresponding homotopies (e.g \texttt{e→ :> e← ∼ id})
also follow but non-trivially (See the \texttt{Agda} source for all details).
\end{proof}

\begin{code}[hide]
  e
    : ∀ (n : ℕ) → (x : ⟦ succ n ⟧)
    --------------------------
    → ⟦ n ⟧ ≃ (⟦ succ n ⟧ ─ x)

  e n x = quasiinverse-to-≃ (e→ n x) ((e← n x ) , (e←:>e→ n x , e→:>e← n x))
    where
\end{code}

\begin{code}[hide]
    e←:>e→
      : ∀ (n : ℕ) → (x : ⟦ succ n ⟧)
      → (e← n  x) :> (e→ n x) ∼ id
\end{code}

\begin{code}[hide]
    e←:>e→ 0 (inl ∗) (inl ∗ , π₄) = ⊥-elim $ π₄ (ap inl idp)
    e←:>e→ (succ n) (inl x) (inl x₁ , π₄) = ⊥-elim (π₄ (ap inl idp))
    e←:>e→ (succ n) (inl x) (inr x₁ , π₄) = pair= (idp , pi-is-prop (λ a x ()) (λ ()) π₄)
    e←:>e→ (succ 0) (inr (inl x)) (inl ∗ , π₄) = pair= (idp , pi-is-prop (λ a x ()) (λ ()) π₄)
    e←:>e→ (succ (succ n)) (inr x) (inl ∗ , π₄) = pair= (idp , pi-is-prop (λ a x ()) (λ ()) π₄)
    e←:>e→ (succ n) (inr x) (inr y , π₄)  = pair= (ooo , pi-is-prop (λ a x ()) _ π₄)
      where
      rec-∼ : (e→ n  x) ∘ (e← n x) ∼ id
      rec-∼ = e←:>e→ n x

      p = (λ x → π₄ (ap inr x))

      j3 : inr {A = 𝟙 ℓ}(π₁ (e→ n x (e← n x (y , p))))
         ≡ inr (π₁ {A = 𝟙 ℓ + ⟦ n ⟧} {λ m → ¬ (m ≡ x)}
              (y , p))

      j3 = ap inr (ap π₁ (rec-∼ (( y , p))))

      ooo
        : π₁ (e→ (succ n) (inr x) (e← (succ n) (inr x) (inr y , π₄)))
        ≡  inr (π₁ {A = 𝟙 ℓ + ⟦ n ⟧} {λ m → ¬ (m ≡ x)}
              (y , p))
      ooo = ap (λ p → π₁ $ (e→ (succ n) (inr x)) p) DEF-g · j3
\end{code}

\begin{code}[hide]
    e→:>e←
      : ∀ (n : ℕ) → (x : ⟦ succ n ⟧)
      → (e→ n  x) :> (e← n x) ∼ id
\end{code}

\begin{code}[hide]
    e→:>e← (succ n) (inl x) (inl x₁) = idp
    e→:>e← (succ n) (inl x) (inr x₁) = idp
    e→:>e← (succ 0) (inr (inl ∗)) (inl ∗) = idp
    e→:>e← (succ (succ n)) (inr x) (inl ∗) = idp
    e→:>e← (succ n) (inr x) (inr y) = ooo
      where
      rec-∼ : (e→ n  x) :> (e← n x) ∼ id
      rec-∼ = e→:>e← n x

      j : e→ (succ n) (inr x) (inr y)
          ≡ (inr (π₁ $ e→ n x y)) , λ p → π₂ (e→ n x y) (inr-is-injective p)
      j = idp

      j1 : e← (succ n) (inr x) (e→ (succ n) (inr x) (inr y))
          ≡ e← (succ n) (inr x) ((inr (π₁ $ e→ n x y)) , λ p → π₂ (e→ n x y) (inr-is-injective p))

      j1 = ap (e← (succ n) (inr x)) j

      j3 : inr {A = 𝟙 ℓ}{⟦ n ⟧} (e← n x ((π₁ $ e→ n x y) , λ p → _))
         ≡ inr (e← n x (e→ n x y))
      j3 = ap inr (ap (e← n x) (pair= (idp , pi-is-prop (λ a x ()) _ _)))

      j4 : inr {A = 𝟙 ℓ}{⟦ n ⟧ }(e← n x (e→ n x y)) ≡ inr y
      j4 = ap inr (rec-∼ y)

      ooo : e← (succ n) (inr x) (e→ (succ n) (inr x) (inr y)) ≡ inr y
      ooo = j1 · DEF-g · j3 · j4
\end{code}

\begin{proposition}\label{e-gives-injective-functions}
The \texttt{e→} and \texttt{e←} functions are both injective functions.
\end{proposition}

\begin{proof} By the equivalence in~\Cref{equivalence-e}, we can get a
(proper) bijection since the corresponding types of that equivalence are in
fact (homotopy) sets. Bijections are injections, so the result follows. For
the function \texttt{e←} repeat the argument but we the symmetry of the
aforementioned equivalence. \end{proof}

\begin{code}[hide]
  e-is-bijection
    : ∀ (n : ℕ) → (x : ⟦ succ n ⟧)
    → isBijection (apply $ e n x)
      ⟦⟧₂-is-set
      (∑-set ⟦⟧₂-is-set
      (λ p → pi-is-set (λ _ → 𝟘-is-set)))

  e-is-bijection n x
    = ≃-to-bijection ⟦⟧₂-is-set (∑-set ⟦⟧₂-is-set (λ p → pi-is-set (λ _ → 𝟘-is-set))) (e n x)
\end{code}

\begin{code}[hide]
  inv-e-is-bijection
    : ∀ (n : ℕ) → (x : ⟦ succ n ⟧)
    → isBijection (apply $ ≃-sym $ e n x)
        (∑-set ⟦⟧₂-is-set (λ p → pi-is-set (λ _ → 𝟘-is-set))) ⟦⟧₂-is-set

  inv-e-is-bijection n x
    = ≃-to-bijection (∑-set ⟦⟧₂-is-set (λ p → pi-is-set (λ _ → 𝟘-is-set))) ⟦⟧₂-is-set (≃-sym $ e n x)
\end{code}

\begin{code}[hide]
  palomar'
    : ∀ (n : ℕ) →  (f : ⟦ succ n ⟧ → ⟦ n ⟧ )
    ----------------------------------------
    → ¬ (isInjective f)

  palomar' 0 f _ = f (inl unit)
  palomar' (succ n) f f-is-inj  = palomar' n g g-is-injective
    where
    h : (⟦ succ (succ n) ⟧ ─ inl unit) → (⟦ succ n ⟧ ─ (f (inl unit)))
    h w@(a , b) = (f a , λ b → π₂ w $ f-is-inj b)

    h-is-inj : isInjective h
    h-is-inj {a₁ , b₁} {(a₂ , b₂)} p
      = pair=
        (f-is-inj (ap π₁ p) ,
        pi-is-prop (λ a x ()) (tr _ (f-is-inj (ap π₁ p)) b₁) b₂)

    g : ⟦ succ n ⟧ → ⟦ n ⟧
    g = lemap (e (succ n) (inl ∗)) :> (h :> remap (e n (f (inl ∗))))

    g-is-injective : isInjective g
    g-is-injective = ∘-injectives-is-injective _ (π₁ $ e-is-bijection _ _) _
                   (∘-injectives-is-injective _ h-is-inj  _ (π₁ $ inv-e-is-bijection _ _))
\end{code}

\section{Proof of \Cref{pigeon-theorem} and other results. }

\begin{proof}[Proof of \Cref{pigeon-theorem}]\label{proof-pigeon-theorem}

The idea here is basically consider the point $x :\equiv \mathsf{inl}
(\mathsf{unit})$ (that represents the first point on each type $[n+1]$ and
$[m+1]$) and its image by the function $f$. Then, we construct a function $h :
[n + 1] - \{x\} \to [ m + 1 ] - \{ x\}$ which acts as the restriction of the
given function $f$. Because $f$ is injective, and any restriction of it is
also injective, $h$ is injective. Now, we do induction on $n$, and the
induction hypothesis says any function $g : [n] → [m]$, $g$ is not injective.

\begin{figure}[!ht]
\begin{center}
\begin{tikzcd}
{[n + 1] - \{ x \}   } \arrow[rr, "h"]       &  & {[m + 1] - \{ f(x) \}   } \arrow[d, "{e^{-1}(m, f(x))}"] \\
{[n]} \arrow[u, "{e(n,x)}"] \arrow[rr, "g"'] &  & {[m]}
\end{tikzcd}
\end{center}
\caption{Construction of the function $g$. In particular, we use $x :\equiv \mathsf{inl}(\mathsf{unit})$. }
\label{diagram}
\end{figure}

But with $h$ we can construct an injective function from $[n] \to [m]$ as
follows. Recall the equivalence functions given by \Cref{equivalence-e}. By
composing $h$ with those functions, as it is stated in the diagram showed
above, we get the function $g$. Since composition of injective functions
yields an injective function (see \Cref{e-gives-injective-functions}),
therefore, $g$ is injective. As we expect by applying the induction
hypothesis, we get the absurd.

The \Agda\ term for this proof is the following.

\begin{code}
  pigeon-theorem
    : ∀ (n m : ℕ)
    → (m < n) → (f : ⟦ n ⟧ → ⟦ m ⟧ )
   --------------------------------------------------------------------------------
   → ¬ (isInjective f)

  pigeon-theorem (succ n) 0       ∗ f f-is-inj = f (inl ∗)
  pigeon-theorem (succ n) (succ m) p f f-is-inj
    = pigeon-theorem n m (succ-<-inj {n = m} p) g g-is-injective
    where
    h : (⟦ succ n ⟧ ─ inl unit) → (⟦ succ m ⟧ ─ (f (inl unit)))
    h w@(a , b) = (f a , λ b → π₂ w $ f-is-inj b)

    h-is-inj : isInjective h
    h-is-inj {a₁ , b₁} {(a₂ , b₂)} p
      = pair= (f-is-inj (ap π₁ p)
              , pi-is-prop (λ a x ()) (tr _ (f-is-inj (ap π₁ p)) b₁) b₂)

    g : ⟦ n ⟧ → ⟦ m ⟧
    g = lemap (e n (inl ∗)) :> h :> remap (e m (f (inl ∗)))

    g-is-injective : isInjective g
    g-is-injective =
      ∘-injectives-is-injective _ (π₁ $ e-is-bijection _ _) _
        (∘-injectives-is-injective _ h-is-inj  _ (π₁ $ inv-e-is-bijection _ _))
\end{code}
\end{proof}

\begin{corollary}
For any $n, m : ℕ$, if $[n] \simeq [m]$ then $n ≡ m$.
\end{corollary}

\begin{proof}

By decidebility of natural numbers, we get an answer whether $n$ is equal to $m$ or not.
If so, we are done. Otherwise, given the equivalence, $e : [n] ≃ [m]$, we consider the
underlined function $f : [n] → [m]$ and its inverse $g$. Now, we can also ask us if $m < n$
or $m > n$. If the former occurs, by \Cref{pigeon-theorem}, $f$ is not injective when it
really is ($f$ is an equivalence). Therefore, from this absurd, the theorem follows.
A similar argument is used when $m >n$ with the function $g$.

\end{proof}


\begin{corollary}[Corollary 2.15.7 in \cite{symmetrybook}]
For any $n,m : ℕ$, if $m < n$ then $\sum_{k : ℕ}\, k < m \not \eq \sum_{k : ℕ}\, k < n$.
\end{corollary}

\bibliographystyle{plain}

\begin{thebibliography}{1}

\bibitem{symmetrybook}
The {Homotopy Type Theory and Univalent Foundations CAS project}.
\newblock {\em {Symmetry Book}}.
\newblock Centre for Advanced Study, at the Norwegian Academy of Science and
  Letters, 2019.

\bibitem{hottbook}
The {Univalent Foundations Program}.
\newblock {\em {Homotopy Type Theory: Univalent Foundations of Mathematics}}.
\newblock Institute for Advanced Study, 2013.

\end{thebibliography}


\end{document}
