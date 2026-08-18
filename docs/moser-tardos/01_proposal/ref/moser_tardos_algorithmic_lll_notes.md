# Algorithmic Lovász Local Lemma: The Moser--Tardos Algorithm

These notes present the Moser--Tardos algorithmic Lovász Local Lemma in the **variable framework**. The purpose is to strengthen the classical Lovász Local Lemma from a non-constructive existence statement into a randomized resampling procedure that actually finds an assignment avoiding all bad events.

The exposition is self-contained. All notation used below is defined before use.

---

## 1. Variable framework

Let

$$
\mathcal X=\{X_1,\ldots,X_n\}
$$

be a finite family of mutually independent random variables. For each $j\in[n]$, the random variable $X_j$ is distributed according to a fixed distribution $\mu_j$ on some state space $\Omega_j$.

The joint distribution of all variables is therefore the product distribution

$$
\mu=\mu_1\otimes\mu_2\otimes\cdots\otimes\mu_n.
$$

Let

$$
\mathcal A=\{A_1,\ldots,A_m\}
$$

be a finite family of undesirable, or **bad**, events.

For each bad event $A\in\mathcal A$, define

$$
\operatorname{vbl}(A)\subseteq\mathcal X
$$

to be a set of variables that determines whether $A$ occurs. Formally, $A$ is measurable with respect to the random variables in $\operatorname{vbl}(A)$.

Thus changing variables outside $\operatorname{vbl}(A)$ cannot change whether $A$ occurs.

The objective is to find an evaluation of all variables in $\mathcal X$ for which no event in $\mathcal A$ occurs.

---

## 2. Dependency graph

Two distinct bad events $A,B\in\mathcal A$ are declared adjacent whenever they depend on at least one common variable:

$$
A\sim B
\quad\Longleftrightarrow\quad
\operatorname{vbl}(A)\cap\operatorname{vbl}(B)\neq\varnothing.
$$

This defines the **variable-overlap dependency graph** on vertex set $\mathcal A$.

For $A\in\mathcal A$, define its neighborhood by

$$
\Gamma(A)
\coloneqq
\{B\in\mathcal A\setminus\{A\}:B\sim A\}.
$$

Define the **inclusive neighborhood**

$$
\Gamma^+(A)
\coloneqq
\Gamma(A)\cup\{A\}.
$$

Because the underlying random variables are mutually independent, an event $A$ is independent of every collection of bad events whose variable sets are disjoint from $\operatorname{vbl}(A)$. Hence this variable-overlap graph is a valid dependency graph in the sense of the classical Lovász Local Lemma.

---

## 3. The LLL condition

Assume that there exist numbers

$$
\alpha_1,\ldots,\alpha_m\in[0,1)
$$

such that, for every $i\in[m]$,

$$
\Pr(A_i)
\le
\alpha_i
\prod_{A_j\in\Gamma(A_i)}
(1-\alpha_j).
\tag{LLL}
$$

It is convenient to regard $\alpha$ as a function on events:

$$
\alpha(A_i)\coloneqq\alpha_i.
$$

Then the condition can be written as

$$
\Pr(A)
\le
\alpha(A)
\prod_{B\in\Gamma(A)}
(1-\alpha(B))
\qquad
\text{for every }A\in\mathcal A.
$$

The classical Lovász Local Lemma says that this condition implies

$$
\Pr\left(
\bigcap_{A\in\mathcal A}\overline A
\right)>0.
$$

The Moser--Tardos theorem proves more: in the variable framework, a very simple resampling algorithm finds such an evaluation efficiently in terms of the expected number of resampling steps.

---

## 4. The Moser--Tardos resampling algorithm

Fix any rule for selecting one currently occurring bad event whenever several bad events occur simultaneously. The analysis does not depend on which such rule is used.

### Algorithm

1. Independently sample every variable $X_j$ according to its original distribution $\mu_j$.
2. While at least one bad event occurs:
   - choose one occurring bad event $A\in\mathcal A$;
   - independently resample every variable in $\operatorname{vbl}(A)$ according to its original distribution;
   - leave every variable outside $\operatorname{vbl}(A)$ unchanged.
3. Stop when no bad event occurs.

A **resampling step** is one execution of the second bullet in Step 2.

The algorithm requires access to the following basic operations:

- drawing an independent fresh sample of each variable $X_j$;
- deciding whether a specified bad event $A_i$ occurs under the current evaluation.

The theorem below bounds the number of resampling steps. The total computational running time additionally depends on the cost of sampling variables and detecting violated events.

---

## 5. Main theorem

### Theorem 5.1 -- Moser--Tardos

Suppose the variable framework above satisfies the LLL condition

$$
\Pr(A_i)
\le
\alpha_i
\prod_{A_j\in\Gamma(A_i)}
(1-\alpha_j)
$$

for some $\alpha_1,\ldots,\alpha_m\in[0,1)$.

For each $i\in[m]$, let $N_i$ denote the number of times the algorithm resamples the event $A_i$.

Then

$$
\mathbb E[N_i]
\le
\frac{\alpha_i}{1-\alpha_i}.
\tag{5.1}
$$

Consequently, if $R$ denotes the total number of resampling steps, then

$$
R=\sum_{i=1}^m N_i
$$

and

$$
\mathbb E[R]
\le
\sum_{i=1}^m
\frac{\alpha_i}{1-\alpha_i}.
\tag{5.2}
$$

In particular, the total number of resampling steps is finite with probability $1$, so the algorithm terminates almost surely. When it terminates, its final evaluation avoids every bad event in $\mathcal A$.

The remainder of these notes proves this theorem.

---

## 6. Execution log

Suppose the algorithm performs at least one resampling step.

The **execution log** is the random sequence

$$
\Lambda=(\Lambda_1,\Lambda_2,\Lambda_3,\ldots),
$$

where $\Lambda_t\in\mathcal A$ is the bad event resampled at the $t$-th resampling step.

If the algorithm terminates after exactly $R$ resamplings, then the execution log is the finite sequence

$$
\Lambda=(\Lambda_1,\ldots,\Lambda_R).
$$

For each $A\in\mathcal A$, the number of occurrences of $A$ in $\Lambda$ is exactly the number of times $A$ is resampled.

The analysis will associate a rooted labeled tree with each position $t$ in the log.

---

## 7. Resampling table

The randomness used by the algorithm may be exposed in advance.

For each variable $X_j$, prepare an infinite independent sequence

$$
X_j^{(0)},X_j^{(1)},X_j^{(2)},\ldots,
$$

where every $X_j^{(s)}$ has distribution $\mu_j$.

Assume that all random variables

$$
\left\{
X_j^{(s)}:
j\in[n],\ s\in\mathbb Z_{\ge0}
\right\}
$$

are mutually independent.

This infinite array is called the **resampling table**.

The algorithm uses the table as follows:

- initially, the value of $X_j$ is $X_j^{(0)}$;
- after $X_j$ has been resampled exactly $s$ times, its new value is $X_j^{(s)}$.

Thus if $X_j$ has already been resampled $s$ times, its current value is $X_j^{(s)}$.

The resampling table does not change the distribution of the algorithm. It merely makes all random choices explicit in a single fixed source of independent randomness.

---

## 8. Witness trees

A witness tree records which previous resamplings can be relevant to a particular later resampling.

### Definition 8.1 -- Witness tree

A **witness tree** is a finite rooted tree $\tau$ together with a labeling map

$$
[u]\in\mathcal A
$$

for every vertex $u$ of $\tau$, such that whenever $v$ is a child of $u$,

$$
[v]\in\Gamma^+([u]).
$$

Equivalently, the event labeling a child is either identical to or adjacent to the event labeling its parent.

A witness tree is called **proper** if distinct children of the same parent have distinct labels.

For a vertex $u$, let

$$
d_\tau(u)
$$

denote the depth of $u$, i.e. its graph distance from the root. The root has depth $0$.

---

## 9. Constructing a witness tree from the execution log

Fix a resampling time $t$.

We define a witness tree

$$
T(\Lambda,t)
$$

from the prefix

$$
\Lambda_1,\ldots,\Lambda_t
$$

of the execution log.

### Construction of $T(\Lambda,t)$

1. Start with a single root vertex labeled by $\Lambda_t$.
2. Process the earlier log entries in reverse chronological order:
   $$
   \Lambda_{t-1},\Lambda_{t-2},\ldots,\Lambda_1.
   $$
3. When processing $\Lambda_s$, check whether there is a current tree vertex $u$ satisfying
   $$
   \Lambda_s\in\Gamma^+([u]).
   $$
4. If no such vertex exists, ignore $\Lambda_s$.
5. If at least one such vertex exists, choose one having maximum depth and attach a new child to it, labeled $\Lambda_s$. Ties among vertices of the same maximum depth may be broken arbitrarily.

The final rooted labeled tree is $T(\Lambda,t)$.

The root is always labeled $\Lambda_t$.

---

## 10. Structural properties of witness trees

### Proposition 10.1

Every tree $T(\Lambda,t)$ produced by the construction above is a proper witness tree.

#### Proof

The parent-child condition holds by construction: a new vertex labeled $\Lambda_s$ is attached only to a vertex $u$ satisfying

$$
\Lambda_s\in\Gamma^+([u]).
$$

It remains to prove properness.

Suppose, for contradiction, that a vertex $u$ has two distinct children $v$ and $w$ with the same label $A$.

Assume $v$ was inserted before $w$ during the reverse scan of the execution log. When $w$ was inserted, $v$ was already present in the tree. Since

$$
[w]=[v]=A
$$

and

$$
A\in\Gamma^+(A),
$$

the vertex $v$ itself was an eligible attachment point for $w$.

But $v$ is one level deeper than its parent $u$. Therefore $u$ could not have been a maximum-depth eligible attachment point for $w$. This contradicts the construction rule.

Hence distinct children of a common parent have distinct labels, and $T(\Lambda,t)$ is proper. $\square$

---

## 11. A depth property

For a vertex $u$ of $T(\Lambda,t)$, define $q(u)$ to be the execution-log time represented by $u$. Thus

$$
[u]=\Lambda_{q(u)}.
$$

The root has $q(u)=t$.

### Lemma 11.1

Let $u$ and $v$ be vertices of $T(\Lambda,t)$. Suppose

$$
q(u)<q(v)
$$

and

$$
\operatorname{vbl}([u])
\cap
\operatorname{vbl}([v])
\neq\varnothing.
$$

Then

$$
d_\tau(u)>d_\tau(v).
$$

#### Proof

Because the construction scans the log backward, the vertex $v$ is already present when the log entry at time $q(u)$ is processed.

Since $[u]$ and $[v]$ share a variable, they are adjacent in the dependency graph. Hence

$$
[u]\in\Gamma([v])
\subseteq
\Gamma^+([v]).
$$

Therefore $v$ is an eligible attachment point when $u$ is inserted.

The construction attaches $u$ below an eligible vertex of maximum depth. Hence the parent of $u$ has depth at least $d_\tau(v)$. Therefore

$$
d_\tau(u)
\ge
d_\tau(v)+1
>
d_\tau(v).
$$

This proves the claim. $\square$

### Corollary 11.2

If two distinct vertices $u$ and $v$ have the same depth, then

$$
\operatorname{vbl}([u])
\cap
\operatorname{vbl}([v])
=
\varnothing.
$$

#### Proof

The log times $q(u)$ and $q(v)$ are distinct. Without loss of generality, suppose $q(u)<q(v)$. If the two labels shared a variable, Lemma 11.1 would imply

$$
d_\tau(u)>d_\tau(v),
$$

contradicting the assumption that they have equal depth. $\square$

Thus all labels appearing at the same level of an execution witness tree depend on pairwise disjoint sets of variables.

---

## 12. Distinct resampling times produce distinct witness trees

### Proposition 12.1

If $s\neq t$, then

$$
T(\Lambda,s)\neq T(\Lambda,t).
$$

#### Proof

If $\Lambda_s\neq\Lambda_t$, then the two witness trees have different root labels, so they are distinct.

Now suppose

$$
\Lambda_s=\Lambda_t=A
$$

and, without loss of generality,

$$
s<t.
$$

Let $t_r$ denote the time of the $r$-th occurrence of $A$ in the execution log. Consider $T(\Lambda,t_r)$.

Every earlier occurrence of $A$ is inserted into this witness tree. Indeed, the root is labeled $A$, and an earlier log entry also labeled $A$ always belongs to the inclusive neighborhood of any existing $A$-labeled vertex because

$$
A\in\Gamma^+(A).
$$

Therefore $T(\Lambda,t_r)$ contains exactly $r$ vertices labeled $A$.

Hence two different occurrences of $A$ in the execution log yield witness trees containing different numbers of $A$-labeled vertices. They cannot be equal.

Thus $T(\Lambda,s)\neq T(\Lambda,t)$ whenever $s\neq t$. $\square$

---

## 13. Counting resamplings by witness trees

For $A\in\mathcal A$, let

$$
\mathcal T_A
$$

denote the set of all finite proper witness trees whose root is labeled $A$.

Let $N_A$ be the number of times $A$ is resampled.

By Proposition 12.1, every occurrence of $A$ in the execution log produces a distinct witness tree rooted at $A$. Conversely, every witness tree occurring in the log with root label $A$ corresponds to a resampling of $A$.

Therefore

$$
N_A
=
\sum_{\tau\in\mathcal T_A}
\mathbf 1
\left[
\exists t:\ T(\Lambda,t)=\tau
\right],
$$

where $\mathbf 1[E]$ denotes the indicator of event $E$.

Taking expectations and using linearity of expectation,

$$
\mathbb E[N_A]
=
\sum_{\tau\in\mathcal T_A}
\Pr
\left[
\exists t:\ T(\Lambda,t)=\tau
\right].
\tag{13.1}
$$

The next lemma bounds each probability in this sum.

---

## 14. Witness-tree coupling lemma

### Lemma 14.1 -- Coupling lemma

Let $\tau$ be a fixed proper witness tree. Then

$$
\Pr
\left[
\exists t:\ T(\Lambda,t)=\tau
\right]
\le
\prod_{u\in V(\tau)}
\Pr([u]),
\tag{14.1}
$$

where $V(\tau)$ denotes the vertex set of $\tau$.

### Proof

We define an auxiliary experiment called the **$\tau$-check**.

#### Step 1: the $\tau$-check

Visit the vertices of $\tau$ in order of decreasing depth. Within one fixed depth, use any order.

When visiting a vertex $u$:

1. independently sample every variable in $\operatorname{vbl}([u])$ according to its original distribution;
2. test whether the event $[u]$ occurs under this fresh evaluation.

The $\tau$-check **passes** if the test succeeds at every vertex.

Every vertex uses fresh samples independent of all samples used at earlier checks. Therefore the tests at distinct vertices are independent, and

$$
\Pr[\text{$\tau$-check passes}]
=
\prod_{u\in V(\tau)}
\Pr([u]).
\tag{14.2}
$$

It remains to couple the $\tau$-check with the Moser--Tardos execution in such a way that

$$
T(\Lambda,t)=\tau
\quad\Longrightarrow\quad
\text{$\tau$-check passes}.
\tag{14.3}
$$

#### Step 2: use the same resampling table

For each variable $X\in\mathcal X$, let

$$
X^{(0)},X^{(1)},X^{(2)},\ldots
$$

be its infinite sequence in the resampling table.

Both the Moser--Tardos algorithm and the $\tau$-check take the next unused value from this sequence whenever they require a fresh sample of $X$.

Assume now that

$$
T(\Lambda,t)=\tau.
$$

Fix a vertex $u\in V(\tau)$ and a variable

$$
X\in\operatorname{vbl}([u]).
$$

Define

$$
S_X(u)
\coloneqq
\left\{
v\in V(\tau):
d_\tau(v)>d_\tau(u)
\text{ and }
X\in\operatorname{vbl}([v])
\right\}.
$$

Because the $\tau$-check processes vertices in decreasing depth, it has sampled $X$ exactly once for every vertex in $S_X(u)$ before reaching $u$.

By Corollary 11.2, no other vertex at the same depth as $u$ depends on $X$. Therefore, when the $\tau$-check visits $u$, the next unused sample of $X$ is

$$
X^{(|S_X(u)|)}.
\tag{14.4}
$$

Now consider the original Moser--Tardos execution immediately before the resampling represented by the vertex $u$, namely immediately before time $q(u)$.

The variable $X$ was sampled once initially, yielding $X^{(0)}$. We claim that the resamplings of $X$ before time $q(u)$ are in one-to-one correspondence with the vertices in $S_X(u)$.

Indeed, suppose $s<q(u)$ and the event $\Lambda_s$ depends on $X$. When the reverse construction reaches time $s$, the vertex $u$ is already present. Since $\Lambda_s$ and $[u]$ both depend on $X$, the event $\Lambda_s$ lies in $\Gamma([u])$, so the log entry at time $s$ is inserted into the witness tree. By Lemma 11.1, its resulting vertex has depth strictly larger than $d_\tau(u)$. Hence it belongs to $S_X(u)$.

Conversely, if $v\in S_X(u)$, then $[v]$ depends on $X$. Also $q(v)$ cannot exceed $q(u)$: if $q(u)<q(v)$, Lemma 11.1 applied to $u$ and $v$ would imply $d_\tau(u)>d_\tau(v)$, contradicting $d_\tau(v)>d_\tau(u)$. Since $u\neq v$, we conclude $q(v)<q(u)$. Thus $v$ represents a resampling of $X$ before time $q(u)$.

Therefore $X$ has been resampled exactly $|S_X(u)|$ times before time $q(u)$. Its current value immediately before the resampling represented by $u$ is consequently

$$
X^{(|S_X(u)|)}.
\tag{14.5}
$$

Equations (14.4) and (14.5) show that, for every variable in $\operatorname{vbl}([u])$, the $\tau$-check uses exactly the same value that the Moser--Tardos execution had immediately before resampling $[u]$.

But the algorithm resamples an event only when that event currently occurs. Hence $[u]$ occurs under this evaluation.

Therefore the $\tau$-check succeeds at $u$. Since $u$ was arbitrary, it succeeds at every vertex of $\tau$.

Thus (14.3) holds. Combining (14.2) and (14.3),

$$
\Pr
\left[
\exists t:\ T(\Lambda,t)=\tau
\right]
\le
\Pr[\text{$\tau$-check passes}]
=
\prod_{u\in V(\tau)}
\Pr([u]).
$$

This proves the lemma. $\square$

---

## 15. First bound on the expected number of resamplings

Substituting Lemma 14.1 into (13.1),

$$
\mathbb E[N_A]
\le
\sum_{\tau\in\mathcal T_A}
\prod_{u\in V(\tau)}
\Pr([u]).
\tag{15.1}
$$

Now apply the LLL condition to every node label:

$$
\Pr([u])
\le
\alpha([u])
\prod_{B\in\Gamma([u])}
(1-\alpha(B)).
$$

Therefore

$$
\mathbb E[N_A]
\le
\sum_{\tau\in\mathcal T_A}
\prod_{u\in V(\tau)}
\left[
\alpha([u])
\prod_{B\in\Gamma([u])}
(1-\alpha(B))
\right].
\tag{15.2}
$$

The remaining task is to prove that the right-hand side converges and to evaluate a useful upper bound for it.

This is done using a random tree process.

---

## 16. Random witness tree: a Galton--Watson process

Fix a bad event $A\in\mathcal A$.

Define a random rooted labeled tree $T_A$ by the following branching process.

### Random-tree process

1. Start with one root labeled $A$.
2. For every currently existing vertex $u$, and independently for every event
   $$
   B\in\Gamma^+([u]),
   $$
   add one child of $u$ labeled $B$ with probability
   $$
   \alpha(B),
   $$
   and add no such child with probability
   $$
   1-\alpha(B).
   $$
3. All choices are mutually independent.
4. Continue level by level.
5. Stop if an entire level produces no new vertices.

The process may, in principle, continue forever. Whenever it terminates, it outputs a finite proper witness tree.

Because at most one child with any given label $B$ is considered for each parent, every finite tree generated by this process is proper.

Moreover, every finite proper witness tree rooted at $A$ has positive generation probability whenever all $\alpha$-values required by its vertices are positive.

---

## 17. Probability of generating a fixed witness tree

For $B\in\mathcal A$, define

$$
\alpha'(B)
\coloneqq
\alpha(B)
\prod_{C\in\Gamma(B)}
(1-\alpha(C)).
\tag{17.1}
$$

### Lemma 17.1 -- Branching-process formula

Let $\tau\in\mathcal T_A$ be a fixed proper witness tree rooted at $A$, and assume $\alpha(A)>0$.

Then

$$
\Pr[T_A=\tau]
=
\frac{1-\alpha(A)}{\alpha(A)}
\prod_{u\in V(\tau)}
\alpha'([u]).
\tag{17.2}
$$

Equivalently,

$$
\Pr[T_A=\tau]
=
\frac{1-\alpha(A)}{\alpha(A)}
\prod_{u\in V(\tau)}
\left[
\alpha([u])
\prod_{B\in\Gamma([u])}
(1-\alpha(B))
\right].
$$

### Proof

For each vertex $u\in V(\tau)$, let

$$
C_\tau(u)
$$

denote the set of labels of the children of $u$ in $\tau$.

Because $\tau$ is proper, every label appears at most once among the children of $u$.

Define

$$
W_u
\coloneqq
\Gamma^+([u])\setminus C_\tau(u).
$$

For the branching process to generate exactly $\tau$:

- every child label in $C_\tau(u)$ must be accepted;
- every label in $W_u$ must be rejected.

Hence

$$
\Pr[T_A=\tau]
=
\prod_{u\in V(\tau)}
\left[
\prod_{B\in C_\tau(u)}\alpha(B)
\right]
\left[
\prod_{B\in W_u}(1-\alpha(B))
\right].
\tag{17.3}
$$

Every non-root vertex appears exactly once as a child of its parent. Therefore

$$
\prod_{u\in V(\tau)}
\prod_{B\in C_\tau(u)}
\alpha(B)
=
\prod_{\substack{v\in V(\tau)\\v\neq r}}
\alpha([v]),
$$

where $r$ is the root.

Since $[r]=A$,

$$
\prod_{\substack{v\in V(\tau)\\v\neq r}}
\alpha([v])
=
\frac{1}{\alpha(A)}
\prod_{v\in V(\tau)}
\alpha([v]).
$$

Thus

$$
\Pr[T_A=\tau]
=
\frac{1}{\alpha(A)}
\prod_{u\in V(\tau)}
\left[
\alpha([u])
\prod_{B\in W_u}
(1-\alpha(B))
\right].
\tag{17.4}
$$

We now simplify the product of rejection probabilities.

For each $u$,

$$
W_u
=
\Gamma^+([u])\setminus C_\tau(u).
$$

Therefore

$$
\prod_{B\in W_u}(1-\alpha(B))
=
\frac{
\prod_{B\in\Gamma^+([u])}(1-\alpha(B))
}{
\prod_{v\text{ child of }u}(1-\alpha([v]))
}.
$$

Multiplying this identity over all vertices $u$, the denominator becomes

$$
\prod_{\substack{v\in V(\tau)\\v\neq r}}
(1-\alpha([v])),
$$

because every non-root vertex is the child of exactly one parent.

The numerator is

$$
\prod_{u\in V(\tau)}
\left[
(1-\alpha([u]))
\prod_{B\in\Gamma([u])}
(1-\alpha(B))
\right].
$$

All factors

$$
1-\alpha([v])
$$

for non-root vertices cancel with the denominator. Only the root factor remains. Since the root label is $A$, this gives

$$
\prod_{u\in V(\tau)}
\prod_{B\in W_u}(1-\alpha(B))
=
(1-\alpha(A))
\prod_{u\in V(\tau)}
\prod_{B\in\Gamma([u])}
(1-\alpha(B)).
$$

Substituting into (17.4),

$$
\Pr[T_A=\tau]
=
\frac{1-\alpha(A)}{\alpha(A)}
\prod_{u\in V(\tau)}
\left[
\alpha([u])
\prod_{B\in\Gamma([u])}
(1-\alpha(B))
\right].
$$

By definition (17.1), this is exactly (17.2). $\square$

---

## 18. Convergence of the witness-tree sum

We now complete the proof of the main theorem.

Fix $A\in\mathcal A$.

If

$$
\alpha(A)=0,
$$

then the LLL condition implies

$$
\Pr(A)=0.
$$

Hence $A$ occurs with probability $0$ under every fresh product-distribution sample, and therefore

$$
\mathbb E[N_A]=0.
$$

Thus the desired bound is trivial in this case.

Assume from now on that

$$
\alpha(A)>0.
$$

Starting from (15.2),

$$
\mathbb E[N_A]
\le
\sum_{\tau\in\mathcal T_A}
\prod_{u\in V(\tau)}
\alpha'([u]).
$$

By Lemma 17.1,

$$
\prod_{u\in V(\tau)}
\alpha'([u])
=
\frac{\alpha(A)}{1-\alpha(A)}
\Pr[T_A=\tau].
$$

Therefore

$$
\mathbb E[N_A]
\le
\frac{\alpha(A)}{1-\alpha(A)}
\sum_{\tau\in\mathcal T_A}
\Pr[T_A=\tau].
$$

The random branching process produces at most one finite tree on each outcome. It may also grow forever. Therefore

$$
\sum_{\tau\in\mathcal T_A}
\Pr[T_A=\tau]
\le1.
$$

Consequently,

$$
\mathbb E[N_A]
\le
\frac{\alpha(A)}{1-\alpha(A)}.
$$

For $A=A_i$, this is

$$
\mathbb E[N_i]
\le
\frac{\alpha_i}{1-\alpha_i}.
$$

This proves (5.1).

Summing over $i\in[m]$ and using linearity of expectation,

$$
\mathbb E[R]
=
\sum_{i=1}^m\mathbb E[N_i]
\le
\sum_{i=1}^m
\frac{\alpha_i}{1-\alpha_i}.
$$

This proves (5.2). $\square$

---

## 19. Almost-sure termination

The theorem gives a finite upper bound on the expectation of the nonnegative extended-integer-valued random variable $R$.

If

$$
\Pr(R=\infty)>0,
$$

then necessarily

$$
\mathbb E[R]=\infty.
$$

Since Theorem 5.1 gives

$$
\mathbb E[R]<\infty,
$$

we must have

$$
\Pr(R<\infty)=1.
$$

Hence the Moser--Tardos algorithm terminates with probability $1$.

At termination, the loop condition is false, so no bad event occurs. Thus the final evaluation belongs to

$$
\bigcap_{i=1}^m\overline{A_i}.
$$

Therefore the Moser--Tardos procedure is a constructive version of the LLL in the variable framework.

---

## 20. Symmetric form

Define

$$
p
\coloneqq
\max_{i\in[m]}\Pr(A_i)
$$

and

$$
d
\coloneqq
\max_{i\in[m]}|\Gamma(A_i)|.
$$

Let $e$ denote the base of the natural logarithm.

Assume

$$
d\ge1
$$

and

$$
ep(d+1)\le1.
\tag{20.1}
$$

Set

$$
\alpha_1=\cdots=\alpha_m
=
\frac{1}{d+1}.
$$

For every $i$,

$$
\alpha_i
\prod_{A_j\in\Gamma(A_i)}
(1-\alpha_j)
=
\frac{1}{d+1}
\left(
\frac{d}{d+1}
\right)^{|\Gamma(A_i)|}.
$$

Since

$$
|\Gamma(A_i)|\le d
$$

and

$$
0<\frac{d}{d+1}<1,
$$

we have

$$
\left(
\frac{d}{d+1}
\right)^{|\Gamma(A_i)|}
\ge
\left(
\frac{d}{d+1}
\right)^d.
$$

Using

$$
\left(1+\frac1d\right)^d\le e,
$$

we obtain

$$
\left(
\frac{d}{d+1}
\right)^d
\ge
\frac1e.
$$

Hence

$$
\alpha_i
\prod_{A_j\in\Gamma(A_i)}
(1-\alpha_j)
\ge
\frac{1}{e(d+1)}.
$$

Condition (20.1) implies

$$
p\le\frac{1}{e(d+1)}.
$$

Therefore the asymmetric LLL condition holds.

Applying Theorem 5.1,

$$
\mathbb E[N_i]
\le
\frac{
\frac1{d+1}
}{
1-\frac1{d+1}
}
=
\frac1d.
$$

Summing over all $m$ bad events,

$$
\mathbb E[R]
\le
\frac{m}{d}.
$$

We have therefore proved the following.

### Corollary 20.1 -- Symmetric Moser--Tardos bound

Suppose $d\ge1$ and

$$
ep(d+1)\le1.
$$

Then the Moser--Tardos algorithm terminates almost surely, outputs an evaluation avoiding every bad event, and performs at most

$$
\frac{m}{d}
$$

resampling steps in expectation.

---

## 21. Why the proof works

The proof has three distinct components.

### 21.1 The execution log converts dynamics into combinatorics

The random execution is summarized by the sequence

$$
\Lambda_1,\Lambda_2,\ldots.
$$

A resampling at time $t$ is represented by a witness tree $T(\Lambda,t)$ encoding the earlier resamplings that can influence it through overlapping variables.

### 21.2 The coupling lemma bounds one fixed witness tree

For a fixed proper witness tree $\tau$,

$$
\Pr[\tau\text{ occurs}]
\le
\prod_{u\in V(\tau)}\Pr([u]).
$$

Thus a large or complicated witness tree is unlikely when all bad events are individually unlikely.

### 21.3 The Galton--Watson process sums over all trees

A direct union bound over all witness trees would require counting a potentially enormous family of trees.

The branching process avoids explicit counting. Its exact tree probabilities satisfy

$$
\Pr[T_A=\tau]
=
\frac{1-\alpha(A)}{\alpha(A)}
\prod_{u\in V(\tau)}
\left[
\alpha([u])
\prod_{B\in\Gamma([u])}
(1-\alpha(B))
\right].
$$

The LLL condition transforms the probability weight of every witness tree into a multiple of a genuine branching-process probability. Since probabilities of mutually exclusive branching-process outcomes sum to at most $1$, the whole witness-tree series converges automatically.

This is the central mechanism behind the expected resampling bound.

---

## 22. Classical LLL versus algorithmic LLL

The classical LLL gives the implication

$$
\text{LLL condition}
\quad\Longrightarrow\quad
\Pr\left(
\bigcap_{i=1}^m\overline{A_i}
\right)>0.
$$

This proves the existence of a good outcome, but does not itself specify how to find one.

In the variable framework, the Moser--Tardos theorem strengthens this to

$$
\text{LLL condition}
\quad\Longrightarrow\quad
\text{the resampling algorithm finds a good evaluation almost surely}.
$$

Moreover,

$$
\mathbb E[R]
\le
\sum_{i=1}^m
\frac{\alpha_i}{1-\alpha_i}.
$$

Thus the same local condition that guarantees existence also controls the expected amount of resampling needed for construction.

---

## 23. Main definitions and statements at a glance

### Variable framework

$$
\mathcal X=\{X_1,\ldots,X_n\}
$$

are mutually independent random variables, and

$$
\mathcal A=\{A_1,\ldots,A_m\}
$$

are bad events, each determined by a subset

$$
\operatorname{vbl}(A_i)\subseteq\mathcal X.
$$

### Dependency neighborhood

$$
\Gamma(A)
=
\left\{
B\in\mathcal A\setminus\{A\}:
\operatorname{vbl}(A)\cap\operatorname{vbl}(B)\neq\varnothing
\right\}.
$$

### Inclusive neighborhood

$$
\Gamma^+(A)
=
\Gamma(A)\cup\{A\}.
$$

### LLL condition

$$
\Pr(A_i)
\le
\alpha_i
\prod_{A_j\in\Gamma(A_i)}
(1-\alpha_j).
$$

### Moser--Tardos algorithm

Repeatedly resample all variables in an occurring bad event until no bad event occurs.

### Expected resampling count

$$
\mathbb E[N_i]
\le
\frac{\alpha_i}{1-\alpha_i}.
$$

### Expected total number of resamplings

$$
\mathbb E[R]
\le
\sum_{i=1}^m
\frac{\alpha_i}{1-\alpha_i}.
$$

### Symmetric condition

If

$$
p=\max_i\Pr(A_i),
\qquad
d=\max_i|\Gamma(A_i)|,
$$

and $d\ge1$ with

$$
ep(d+1)\le1,
$$

then

$$
\mathbb E[R]
\le
\frac{m}{d}.
$$

---

## 24. Proof roadmap

The logical structure of the Moser--Tardos analysis is

$$
\text{resampling algorithm}
\longrightarrow
\text{execution log}
\longrightarrow
\text{witness trees}
\longrightarrow
\text{coupling bound}
\longrightarrow
\text{Galton--Watson process}
\longrightarrow
\text{finite expected resampling count}.
$$

More explicitly,

$$
\mathbb E[N_A]
=
\sum_{\tau\in\mathcal T_A}
\Pr[\tau\text{ occurs}]
$$

and the coupling lemma gives

$$
\mathbb E[N_A]
\le
\sum_{\tau\in\mathcal T_A}
\prod_{u\in V(\tau)}
\Pr([u]).
$$

The LLL condition gives

$$
\prod_{u\in V(\tau)}
\Pr([u])
\le
\prod_{u\in V(\tau)}
\left[
\alpha([u])
\prod_{B\in\Gamma([u])}
(1-\alpha(B))
\right].
$$

Finally, the branching-process formula converts the latter quantity into

$$
\frac{\alpha(A)}{1-\alpha(A)}
\Pr[T_A=\tau].
$$

Therefore

$$
\mathbb E[N_A]
\le
\frac{\alpha(A)}{1-\alpha(A)}
\sum_{\tau\in\mathcal T_A}
\Pr[T_A=\tau]
\le
\frac{\alpha(A)}{1-\alpha(A)}.
$$

This is the core argument of the Moser--Tardos theorem.
