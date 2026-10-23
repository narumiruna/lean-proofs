<a id="chapter-02"></a>

# Chapter 2 — Basic Topology

[All chapters](../solutions.md) · [Previous chapter](chapter-01.md) · [Next chapter](chapter-03.md)

**Exercises:** [1](#r02e01) · [2](#r02e02) · [3](#r02e03) · [4](#r02e04) · [5](#r02e05) · [6](#r02e06) · [7](#r02e07) · [8](#r02e08) · [9](#r02e09) · [10](#r02e10) · [11](#r02e11) · [12](#r02e12) · [13](#r02e13) · [14](#r02e14) · [15](#r02e15) · [16](#r02e16) · [17](#r02e17) · [18](#r02e18) · [19](#r02e19) · [20](#r02e20) · [21](#r02e21) · [22](#r02e22) · [23](#r02e23) · [24](#r02e24) · [25](#r02e25) · [26](#r02e26) · [27](#r02e27) · [28](#r02e28) · [29](#r02e29) · [30](#r02e30)

<a id="r02e01"></a>
### 2.1 — The empty subset
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter02/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** For every set $A$ in any ambient set, $\varnothing\subseteq A$.

**Proof.** The assertion requires that each member of $\varnothing$ belong to $A$. There is no member of $\varnothing$, so the implication holds.

**Lean declarations:** `exercise01`.

<a id="r02e02"></a>
### 2.2 — Countably infinitely many algebraic numbers
**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter02/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** A complex number is algebraic if it is a root of a nonzero polynomial with integer coefficients. The set of algebraic complex numbers is countably infinite. In a displayed finite coefficient list, the coefficients must not all vanish; the coefficient at the last displayed index need not be nonzero.

**Proof.** Integer polynomials form an at most countable set: each is specified by a finite list of integers. Each nonzero polynomial has finitely many complex roots. Thus the algebraic numbers form a countable union of finite sets and are at most countable. For every $n\in\mathbb N$, the polynomial $X-n$ is nonzero and has root $n$. These roots are distinct, so the set is infinite.

**Lean declarations:** `exercise02`.

<a id="r02e03"></a>
### 2.3 — A transcendental real number exists
**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter02/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** There exists $x\in\mathbb R$ such that $p(x)\ne0$ for every nonzero $p\in\mathbb Z[X]$.

**Proof.** There are at most countably many integer polynomials, and each nonzero polynomial has finitely many real roots. Their real roots therefore form an at most countable set. Since $\mathbb R$ is uncountable, some real number lies outside this set. It satisfies the required condition.

**Lean declarations:** `exercise03`.

<a id="r02e04"></a>
### 2.4 — Irrational numbers are uncountable
**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter02/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** The set $\mathbb R\setminus\mathbb Q$ is uncountable.

**Proof.** The rational numbers are countable. If the irrational numbers were at most countable, their union with the rationals would make $\mathbb R$ at most countable. This contradicts the uncountability of $\mathbb R$.

**Lean declarations:** `exercise04`.

<a id="r02e05"></a>
### 2.5 — Exactly three accumulation points
**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter02/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** The bounded set

$$
E=\{1/n:n\ge1\}\cup\{2+1/n:n\ge1\}\cup\{4+1/n:n\ge1\},
$$

where $n$ is an integer, has derived set $E'=\{0,2,4\}$, which has exactly three elements.

**Proof.** Each term lies in $[0,5]$, so $E$ is bounded. For each $a\in\{0,2,4\}$, the distinct points $a+1/n$ converge to $a$, making $a$ an accumulation point. No other point is an accumulation point of this sequence: a neighborhood separated from its limit meets only finitely many terms, and a smaller punctured neighborhood avoids those terms. The derived set of a finite union is the union of its derived sets. Indeed, a point outside all these derived sets has a punctured neighborhood avoiding each set, and the finite intersection of those neighborhoods avoids the union. Thus $E'=\{0,2,4\}$; these three real numbers are distinct.

**Lean declarations:** `exercise05`.

<a id="r02e06"></a>
### 2.6 — Derived sets and closure
**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter02/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** For a subset $E$ of a metric space, its derived set $E'$ is closed, and

$$
\overline E=E\cup E',\qquad (\overline E)'=E'.
$$

However, $E$ and $E'$ need not have the same accumulation points.

**Proof.** If $x\notin E'$, choose $r>0$ such that $B(x,r)\cap E\subseteq\{x\}$. Every $y\in B(x,r)$ distinct from $x$ has a small ball contained in $B(x,r)$ and avoiding $x$, hence avoiding $E$. Neither such a $y$ nor $x$ belongs to $E'$. Thus the complement of $E'$ is open, and $E'$ is closed.

A point of $\overline E$ either belongs to $E$ or has another point of $E$ in each neighborhood. This proves $\overline E=E\cup E'$. Monotonicity gives $E'\subseteq(\overline E)'$. For the reverse inclusion, if $x\notin E'$, choose the ball above. Every other point of that ball has a neighborhood disjoint from $E$, so $B(x,r)\cap\overline E\subseteq\{x\}$. Hence $x\notin(\overline E)'$.

For a counterexample, take $E=\{1/n:n\ge1\}\subset\mathbb R$. Its only accumulation point is $0$, so $E'=\{0\}$. A finite set has no accumulation points, giving $(E')'=\varnothing\ne E'$.

**Lean declarations:** `exercise06_derived_closed`, `exercise06_closure_limit_points`, `exercise06_derived_limit_points`, `exercise06_counterexample`.

<a id="r02e07"></a>
### 2.7 — Closure of finite and countable unions
**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter02/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $A_i$ be subsets of a metric space. For every integer $n\ge0$,

$$
\overline{\bigcup_{i=1}^{n}A_i}=\bigcup_{i=1}^{n}\overline{A_i}.
$$

For the countable union,

$$
\bigcup_{i=1}^{\infty}\overline{A_i}\subseteq
\overline{\bigcup_{i=1}^{\infty}A_i},
$$

and strict containment can occur.

**Proof.** Each $A_i$ lies in the union, so monotonicity of closure gives the inclusion from the union of closures into the closure of the union. For a finite family, the union of the closures is closed and contains every $A_i$, so it also contains the closure of their union. When $n=0$, both sets are empty.

For strictness, put $A_i=\{1/i\}\subset\mathbb R$ for $i\ge1$. Each singleton is closed, so the union of their closures does not contain $0$. But $1/i\to0$, so $0$ belongs to the closure of their union.

**Lean declarations:** `exercise07a`, `exercise07b_inclusion`, `exercise07b_strict`.

<a id="r02e08"></a>
### 2.8 — Accumulation points of open and closed plane sets
**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter02/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Every member of an open subset of Euclidean $\mathbb R^2$ is an accumulation point of that set. This assertion is false for closed subsets.

**Proof.** If $x\in E$ and $E$ is open, some ball $B(x,r)$ lies in $E$. Every neighborhood of $x$ contains a point on a sufficiently short, nonzero line segment from $x$ inside that ball. Thus it contains a point of $E$ other than $x$. In contrast, $E=\{(0,0)\}$ is closed, contains the origin, and has no point different from the origin. The origin is not an accumulation point.

**Lean declarations:** `exercise08_open`, `exercise08_closed`.

<a id="r02e09"></a>
### 2.9 — Interior and its limits
**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter02/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be a subset of a metric space $X$, and write $E^\circ$ for its interior.

1. $E^\circ$ is open.
2. $E$ is open if and only if $E^\circ=E$.
3. If $G$ is open and $G\subseteq E$, then $G\subseteq E^\circ$.
4. $X\setminus E^\circ=\overline{X\setminus E}$.
5. $E^\circ$ need not equal $(\overline E)^\circ$.
6. $\overline E$ need not equal $\overline{E^\circ}$.

**Proof.** The interior is the union of all open subsets of $E$. Unions of open sets are open, proving the first assertion, and every open subset of $E$ lies in this union, proving the third. If $E$ is open, it is one of those subsets, so $E^\circ=E$. Conversely, equality with the open set $E^\circ$ makes $E$ open.

A point lies outside $E^\circ$ exactly when every neighborhood meets $X\setminus E$. This is the definition of membership in $\overline{X\setminus E}$ and proves the fourth assertion.

For the fifth, take $E=\mathbb R\setminus\{0\}$. It is open and dense, so $E^\circ=E$ whereas $(\overline E)^\circ=\mathbb R$. For the sixth, take $E=\{0\}\subset\mathbb R$. Its closure is itself, but its interior and the closure of its interior are empty.

**Lean declarations:** `exercise09a`, `exercise09b`, `exercise09c`, `exercise09d`, `exercise09e`, `exercise09f`.

<a id="r02e10"></a>
### 2.10 — The zero-one metric
**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter02/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** On an infinite set $X$, define $d(x,y)=0$ if $x=y$, and $d(x,y)=1$ otherwise. This is a metric. Every subset is open and closed, and a subset is compact if and only if it is finite, including the empty set. The same conclusions hold without the assumption that $X$ is infinite.

**Proof.** Nonnegativity, symmetry, and $d(x,y)=0\iff x=y$ follow from the definition. If $x=z$, the triangle inequality is immediate. If $x\ne z$, at least one of $x\ne y$ and $y\ne z$ holds, so $1=d(x,z)\le d(x,y)+d(y,z)$.

Since $B(x,1/2)=\{x\}$, all singletons are open. Every set is a union of singletons and is therefore open; its complement is open as well, so it is closed. A finite set is compact by choosing one cover member for each point. For an infinite set, the cover by its open singletons has no finite subcover. The empty set has the empty finite subcover.

**Lean declarations:** `zeroOneDistance_metric_axioms`, `zeroOne_isOpen`, `zeroOne_isClosed`, `zeroOne_isCompact_iff`.

<a id="r02e11"></a>
### 2.11 — Five proposed metrics on the real line
**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter02/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** For $x,y\in\mathbb R$, consider

$$
\begin{aligned}
d_1(x,y)&=(x-y)^2,&d_2(x,y)&=\sqrt{|x-y|},\\
d_3(x,y)&=|x^2-y^2|,&d_4(x,y)&=|x-2y|,\\
d_5(x,y)&=\frac{|x-y|}{1+|x-y|}.
\end{aligned}
$$

Exactly $d_2$ and $d_5$ are metrics.

**Proof.** For $d_1$, the triangle inequality fails because $d_1(0,2)=4>1+1=d_1(0,1)+d_1(1,2)$. For $d_3$, separation fails: $1\ne-1$ but $d_3(1,-1)=0$. For $d_4$, both the diagonal and symmetry axioms fail: $d_4(1,1)=1\ne0$, while $d_4(0,1)=2\ne1=d_4(1,0)$.

Both $d_2$ and $d_5$ are nonnegative, symmetric, and vanish exactly when $x=y$. To prove their triangle inequalities, put $a=|x-y|$, $b=|y-z|$, and $c=|x-z|$. Then $a,b,c\ge0$ and $c\le a+b$. Since

$$
(\sqrt a+\sqrt b)^2=a+b+2\sqrt{ab}\ge c,
$$

comparison of nonnegative square roots proves the inequality for $d_2$. For $d_5$, positive denominators give

$$
\frac{c}{1+c}\le\frac{a+b}{1+a+b}
=\frac a{1+a+b}+\frac b{1+a+b}
\le\frac a{1+a}+\frac b{1+b}.
$$

Thus both positive cases satisfy all metric axioms.

**Lean declarations:** `distanceOne_not_metric`, `distanceOne_triangle_failure`, `distanceTwo_metric`, `distanceThree_not_metric`, `distanceThree_separation_failure`, `distanceFour_not_metric`, `distanceFour_diagonal_failure`, `distanceFour_symmetry_failure`, `distanceFive_metric`, `exercise11`.

<a id="r02e12"></a>
### 2.12 — Direct compactness of a sequence and its limit
**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter02/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** The set

$$
K=\{0\}\cup\{1/n:n\ge1\}\subset\mathbb R
$$

is compact. More explicitly, every indexed open cover of $K$ has a finite subcover, without using the Heine–Borel theorem.

**Proof.** Let $(U_i)_{i\in I}$ be an open cover. Choose $i_0$ with $0\in U_{i_0}$. Since $1/n\to0$, there is $N\ge1$ such that $1/n\in U_{i_0}$ whenever $n\ge N$. For each of the finitely many remaining terms, choose one cover member containing it. Those finitely many members together with $U_{i_0}$ cover $K$. This is the open-cover definition of compactness.

The same argument applies to a sequence together with its limit in any topological space. For this particular sequence, $K$ is countably infinite and $K'=\{0\}$: the reciprocals are distinct and positive, converge to $0$, and any point different from $0$ has a neighborhood meeting only finitely many of them. Adding the singleton $\{0\}$ creates no further accumulation point.

**Lean declarations:** `reciprocalSet_finite_subcover`, `exercise12`.

<a id="r02e13"></a>
### 2.13 — A compact set with countably infinite derived set
**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter02/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $A=\{0\}\cup\{1/n:n\ge1\}$ and

$$
K=A+A=\{a+b:a,b\in A\}.
$$

Then $K$ is compact and $K'=A$. In particular, its set of accumulation points is countably infinite, not merely at most countable.

**Proof.** By Exercise 2.12, $A$ is compact. The addition map is continuous on the compact product $A\times A$, so its image $K$ is compact. If $a\in A$, the points $a+1/n\in K$ differ from $a$ and converge to $a$. Thus $A\subseteq K'$.

Conversely, let $x\in K'$. Choose a sequence $u_j\in K\setminus\{x\}$ converging to $x$, and write $u_j=a_j+b_j$ with $a_j,b_j\in A$. Compactness of $A\times A$ gives a subsequence for which $(a_j,b_j)\to(a,b)\in A\times A$. Continuity and uniqueness of limits give $x=a+b$. Every nonzero point of $A$ is isolated in $A$. Thus if both $a$ and $b$ were nonzero, both summand sequences would eventually be constant, making $u_j=x$, a contradiction. One of $a,b$ is zero, so $x\in A$. This proves $K'=A$, and $A$ is countably infinite.

**Lean declarations:** `exercise13`.

<a id="r02e14"></a>
### 2.14 — An open cover without a finite subcover
**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter02/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** The family $U_t=(t,\infty)$, indexed by all positive real numbers $t$, covers $(0,1)$, but no finite subfamily covers $(0,1)$.

**Proof.** Each $U_t$ is open. If $0<x<1$, then $t=x/2>0$ and $x\in U_t$, proving coverage. Given a nonempty finite set of positive indices, let $m$ be its minimum and take $x=\min(1,m)/2$. Then $0<x<1$ and $x<t$ for every selected index, so $x$ lies in none of the selected rays. The empty subfamily also fails to cover, for example because it misses $1/2$.

**Lean declarations:** `exercise14`.

<a id="r02e15"></a>
### 2.15 — Closedness or boundedness alone is insufficient
**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter02/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** The compact-set finite-intersection theorem and its decreasing-sequence corollary both fail if compactness is replaced by closedness alone. They also both fail if it is replaced by boundedness alone.

**Proof.** For $n\ge0$, let $F_n=[n,\infty)\subset\mathbb R$. These sets are closed, nonempty, and decreasing. Every nonempty finite intersection equals the member with largest index and is therefore nonempty; the intersection of the empty family is $\mathbb R$. However, no real number is at least every natural number, so $\bigcap_{n\ge0}F_n=\varnothing$. This gives both closed-set counterexamples.

For the bounded-set counterexamples, let $B_n=(0,1/(n+1))$. These sets are bounded, nonempty, and decreasing. Their finite intersections are nonempty by the same largest-index argument, including the empty family as above. A member of their total intersection would be positive and less than $1/(n+1)$ for every $n$, which contradicts $1/(n+1)\to0$. Thus the total intersection is empty. These are separate replacements of compactness, not a counterexample under joint closedness and boundedness in $\mathbb R$.

**Lean declarations:** `closed_finite_intersection_counterexample`, `closed_nested_counterexample`, `bounded_finite_intersection_counterexample`, `bounded_nested_counterexample`.

<a id="r02e16"></a>
### 2.16 — A clopen bounded noncompact subset of the rationals
**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter02/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** In $\mathbb Q$ with its usual metric, the set

$$
E=\{q\in\mathbb Q:2<q^2<3\}
$$

is closed and bounded but not compact. It is also open in $\mathbb Q$.

**Proof.** The map $q\mapsto q^2$ is continuous, so $E$ is the inverse image of $(2,3)$ and is open. Since $\sqrt2$ and $\sqrt3$ are irrational, no rational square equals $2$ or $3$. Thus $E$ is also the inverse image of the closed interval $[2,3]$ and is closed. Its members satisfy $|q|<2$, proving boundedness.

Suppose $E$ were compact. It is nonempty because $3/2\in E$. The continuous real-valued function $q\mapsto q^2$ would attain a minimum at some $q\in E$. But $\sqrt2<|q|$, so density of the rationals gives $r\in\mathbb Q$ with $\sqrt2<r<|q|$. Consequently $2<r^2<q^2<3$, so $r\in E$ has a smaller square, a contradiction. All topological claims here are relative to $\mathbb Q$.

**Lean declarations:** `rationalSquareBand_isClosed`, `rationalSquareBand_isBounded`, `rationalSquareBand_not_isCompact`, `rationalSquareBand_isOpen`, `exercise16`.

<a id="r02e17"></a>
### 2.17 — Decimal expansions using only 4 and 7
**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter02/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** Let

$$
E=\left\{\sum_{n=0}^{\infty}\frac{d_n}{10^{n+1}}:d_n\in\{4,7\}\right\}\subseteq[0,1].
$$

Then $E$ is uncountable, is not dense in $[0,1]$, is compact, and is perfect: it is closed and every member is an accumulation point. Each permitted expansion is unique even among expansions using all ten decimal digits.

**Proof.** Encode digits by binary sequences, with $0$ selecting $4$ and $1$ selecting $7$. This defines a continuous map $f:\{0,1\}^{\mathbb N}\to\mathbb R$: agreement through the first $N$ digits bounds the remaining difference by a geometric tail tending to zero. Its image is exactly $E$. The binary sequence space is compact, so $E$ is compact and therefore closed.

To check uniqueness, every tail consisting of digits $4$ and $7$ has decimal value strictly between $0$ and $1$. If such an expansion and any other decimal expansion first differed at position $n$, cancellation of the common prefix and multiplication by $10^{n+1}$ would give

$$
d_n+u=e_n+v,\qquad 0<u<1,\quad 0\le v\le1.
$$

If $d_n>e_n$, the left side exceeds $e_n+1$; if $d_n<e_n$, it is less than $e_n$. Both contradict the equality. Thus no position differs. In particular, $f$ is injective, and terminating-versus-repeating-nine ambiguity cannot affect $E$.

Binary sequence space is uncountable by Cantor's diagonal argument: from a purported enumeration $a^{(n)}$, the sequence whose $n$th bit is the opposite of $a^{(n)}_n$ is omitted. Injectivity of $f$ makes $E$ uncountable. For any permitted digit sequence, change just its $n$th digit. The resulting values differ from the original value and converge to it as $n\to\infty$. Thus there are no isolated points. Finally, the first digit gives $x\ge4/10$ for all $x\in E$. Since $E$ is closed, $0\notin\overline E$, although $0\in[0,1]$. Equivalently, the relatively open neighborhood $[0,4/10)$ is disjoint from $E$, so density also fails in the subspace topology of $[0,1]$.

**Lean declarations:** `decimal47Set_not_countable`, `decimal47Set_not_dense`, `decimal47Set_not_dense_subspace`, `decimal47Set_isCompact`, `decimal47Set_perfect`, `decimal47Set_isClosed`, `decimal47Set_no_isolated`.

<a id="r02e18"></a>
### 2.18 — A perfect set containing only irrational numbers
**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter02/Exercise18.lean).
**Inventory status:** Verified as stated.

**Statement.** There exists a nonempty compact perfect set $P\subset\mathbb R$ with $P\cap\mathbb Q=\varnothing$. In particular, a nonempty closed set with no isolated points can contain no rational number.

**Proof.** The source uses standard Polish-space results. First, $\mathbb R\setminus\mathbb Q$ is uncountable, because otherwise its union with the countable set $\mathbb Q$ would make $\mathbb R$ countable. Since $\mathbb Q$ is Borel, the Polish topology refinement theorem supplies a finer Polish topology on $\mathbb R$ in which its complement is closed. The perfect-set theorem for uncountable closed subsets of Polish spaces then gives a continuous injection

$$
f:\{0,1\}^{\mathbb N}\longrightarrow\mathbb R\setminus\mathbb Q
$$

for that finer topology. The identity map from the finer topology to the usual topology is continuous, so $f$ is also continuous as an ordinary real-valued map.

Set $P=f(\{0,1\}^{\mathbb N})$. Its domain is nonempty and compact, so $P$ is nonempty and compact in the usual real topology, hence closed. To show that $f(a)$ is not isolated, flip only the $n$th bit of $a$. These distinct sequences converge to $a$ in the product topology; continuity gives convergence of their images to $f(a)$, and injectivity makes all those images different from $f(a)$. Thus $P$ is perfect. Its construction places every member outside $\mathbb Q$. The finer topology is only a proof tool; every stated property of $P$ uses the usual topology.

**Lean declarations:** `exists_nonempty_perfect_irrational_set`.

<a id="r02e19"></a>
### 2.19 — Separation and uncountability of connected spaces
**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter02/Exercise19.lean).
**Inventory status:** Verified as stated.

**Statement.** Subsets $A,B$ of a metric space are *separated* when

$$
\overline A\cap B=\varnothing,\qquad A\cap\overline B=\varnothing.
$$

This does not require disjoint closures or positive distance.

1. Disjoint closed sets are separated.
2. Disjoint open sets are separated.
3. For $p\in X$ and $\delta>0$, the sets $\{q:d(p,q)<\delta\}$ and $\{q:d(p,q)>\delta\}$ are separated. The Lean result holds for every real $\delta$.
4. A connected metric space with two distinct points is uncountable.

**Proof.** For closed sets, replace each closure by the set itself. If $A$ and $B$ are disjoint and open, a point of $B$ has the neighborhood $B$ disjoint from $A$, so it cannot belong to $\overline A$; the other condition follows symmetrically. The two sets in the third assertion are disjoint and open by continuity of $q\mapsto d(p,q)$, so the second assertion applies for every $\delta$.

For the fourth, let $a\ne b$. The continuous image of $X$ under $x\mapsto d(a,x)$ is connected and contains both $0$ and $d(a,b)>0$. A connected subset of the real line contains the interval between any two of its points, so the image contains $[0,d(a,b)]$. That nondegenerate interval is uncountable. If $X$ were at most countable, its image would be at most countable, a contradiction.

**Lean declarations:** `exercise19_a`, `exercise19_b`, `exercise19_c`, `exercise19_d`.

<a id="r02e20"></a>
### 2.20 — Connected closure and disconnected interior
**Lean source:** [Exercise20.lean](../../../Math/Rudin/Chapter02/Exercise20.lean).
**Inventory status:** Verified as stated.

**Statement.** The closure of a connected set is connected. This holds in every topological space, with the empty set allowed as connected in Rudin's convention. The interior of a connected set need not be connected, even in $\mathbb R^2$.

**Proof.** A dense connected subset of a space forces that space to be connected: any separation of the space into two nonempty relatively open sets meets the dense subset on both sides and would separate it. Apply this observation to $E\subseteq\overline E$. The empty case has empty closure.

For the interior, take

$$
S=\{(x,y)\in\mathbb R^2:x\ne0\}\cup\{(0,0)\}.
$$

For every $p\in S$, the segment from the origin to $p$ lies in $S$: a positive multiple of a point with nonzero first coordinate still has nonzero first coordinate, and the zero multiple is the origin. Hence $S$ is star-convex, thus path connected and connected. Its interior is exactly $\{(x,y):x\ne0\}$. That set is open, while the added origin is not interior because every ball about it contains a nonzero point on the vertical axis, outside $S$. The interior is the disjoint union of the two nonempty open half-planes $x<0$ and $x>0$, so it is disconnected.

**Lean declarations:** `exercise20_closure_connected`, `exercise20_interior_counterexample`.

<a id="r02e21"></a>
### 2.21 — Separated sets and line segments
**Lean source:** [Exercise21.lean](../../../Math/Rudin/Chapter02/Exercise21.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $A,B\subseteq\mathbb R^k$ be separated, and define $p(t)=(1-t)a+tb$ for all real $t$.

1. For any $a,b\in\mathbb R^k$, the preimages $A_0=p^{-1}(A)$ and $B_0=p^{-1}(B)$ are separated subsets of $\mathbb R$.
2. If $a\in A$ and $b\in B$, some $t_0\in(0,1)$ satisfies $p(t_0)\notin A\cup B$.
3. Every convex subset of $\mathbb R^k$ is connected, including the empty set. The results allow $k=0$.

**Proof.** The map $p$ is continuous. For any set $D$, continuity gives $\overline{p^{-1}(D)}\subseteq p^{-1}(\overline D)$. Applying this to $A$ and $B$, the two separation conditions pull back to give the first assertion.

For the second, suppose the entire segment $C=p([0,1])$ lay in $A\cup B$. It is connected as the continuous image of $[0,1]$ and meets both $A$ and $B$. The sets $C\cap A$ and $C\cap B$ are disjoint and nonempty. They are relatively closed in $C$: for example, $C\cap\overline A=C\cap A$, since no point of $B$ lies in $\overline A$. They therefore separate $C$, a contradiction. Some segment point is outside $A\cup B$, and it cannot be either endpoint, so its parameter lies strictly between $0$ and $1$.

If a convex set had a separation into two nonempty parts, choose one point in each. Convexity puts the whole segment between them in the set, contrary to the second assertion. Hence it is connected; the empty case has no such separation.

**Lean declarations:** `exercise21_a`, `exercise21_b`, `exercise21_c`.

<a id="r02e22"></a>
### 2.22 — Rational coordinates give separability
**Lean source:** [Exercise22.lean](../../../Math/Rudin/Chapter02/Exercise22.lean).
**Inventory status:** Verified as stated.

**Statement.** Euclidean $\mathbb R^k$ has the at most countable dense subset $\mathbb Q^k$. This proves separability for positive integers $k$ and also for $k=0$.

**Proof.** A finite product of countable sets is countable, so the rational-coordinate points are at most countable. For $k>0$, given $x\in\mathbb R^k$ and $\varepsilon>0$, choose rational $q_i$ with $|q_i-x_i|<\varepsilon/\sqrt{k}$ for each coordinate. Then

$$
\|q-x\|_2^2=\sum_{i=1}^{k}|q_i-x_i|^2<\varepsilon^2,
$$

so every ball meets $\mathbb Q^k$. Equivalently, this is density of the finite product of the dense rational subsets, under the usual product–Euclidean homeomorphism used in Lean. For $k=0$, the Euclidean space and its rational-coordinate subset each consist of the single empty tuple.

**Lean declarations:** `exercise22_countable`, `exercise22_dense`, `exercise22`.

<a id="r02e23"></a>
### 2.23 — A countable base from a dense set
**Lean source:** [Exercise23.lean](../../../Math/Rudin/Chapter02/Exercise23.lean).
**Inventory status:** Verified as stated.

**Statement.** If a metric space $X$ has an at most countable dense subset $D$, then it has an at most countable family $\mathcal B$ of open sets such that, for every open $G$ and $x\in G$, some $V\in\mathcal B$ satisfies $x\in V\subseteq G$. Finite and empty spaces are included.

**Proof.** This is the standard theorem that a separable metric space is second countable, used in Lean. Explicitly, take all balls $B(d,r)$ with $d\in D$ and positive rational $r$. They form an at most countable family of open sets. Given $x\in G$, choose $\varepsilon>0$ with $B(x,\varepsilon)\subseteq G$. Density gives $d\in D$ with $d(x,d)<\varepsilon/3$. Choose a rational radius with

$$
d(x,d)<r<\varepsilon-d(x,d).
$$

Then $x\in B(d,r)$, and the triangle inequality gives $B(d,r)\subseteq B(x,\varepsilon)\subseteq G$. If $X$ is empty, the empty family satisfies the condition vacuously.

**Lean declarations:** `exercise23`.

<a id="r02e24"></a>
### 2.24 — Accumulation points imply separability
**Lean source:** [Exercise24.lean](../../../Math/Rudin/Chapter02/Exercise24.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose that every infinite subset $E$ of a metric space $X$ has an accumulation point in $X$. Then $X$ has an at most countable dense subset. No infinitude or nonemptiness assumption on $X$ is needed.

**Proof.** The source first proves a stronger intermediate result: $X$ is compact. It uses the standard characterization of countable compactness by accumulation points of infinite subsets, followed by the metric-space implications from countable compactness to sequential compactness and from sequential compactness to compactness. These theorems apply to the stated hypothesis without a nonemptiness assumption.

To see how compactness gives the conclusion, for each $n\ge1$ choose a finite subcover from the cover by balls of radius $1/n$, and let $D_n$ be their centers. The set $D=\bigcup_{n\ge1}D_n$ is at most countable. Given a nonempty ball $B(x,\varepsilon)$, choose $n$ with $1/n<\varepsilon$. Some selected center lies within $1/n$ of $x$, hence in that ball. Thus $D$ is dense. In the empty space, all the finite center sets can be empty. The Lean proof uses these compactness equivalences rather than the exercise's suggested separated-point construction.

**Lean declarations:** `compact_of_infinite_accumulation`, `exercise24`.

<a id="r02e25"></a>
### 2.25 — Compact metric spaces are separable and second countable
**Lean source:** [Exercise25.lean](../../../Math/Rudin/Chapter02/Exercise25.lean).
**Inventory status:** Verified as stated.

**Statement.** Every compact metric space $X$ has an at most countable dense subset and an at most countable base of open sets. The base refines every open neighborhood: if $x\in G$ and $G$ is open, some base member $V$ satisfies $x\in V\subseteq G$.

**Proof.** For each positive integer $n$, compactness selects finitely many radius-$1/n$ balls covering $X$. The union of their centers over all $n$ is at most countable and dense: for any $x$ and any $\varepsilon>0$, a selected center is within $1/n<\varepsilon$ of $x$ for sufficiently large $n$. Apply Exercise 2.23 to this dense subset to obtain the base and its refinement property. For the empty space, both the dense set and the base may be empty; finite spaces are also included.

**Lean declarations:** `exercise25_base`, `exercise25_separable`.

<a id="r02e26"></a>
### 2.26 — Accumulation points imply the finite-subcover property
**Lean source:** [Exercise26.lean](../../../Math/Rudin/Chapter02/Exercise26.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X$ be a metric space in which every infinite subset has an accumulation point in $X$. For any index set $I$ and any open cover $(U_i)_{i\in I}$ of $X$, there is a finite $J\subseteq I$ with $X\subseteq\bigcup_{i\in J}U_i$.

**Proof.** As established in Exercise 2.24, the accumulation-point hypothesis implies countable compactness, hence sequential compactness and compactness in a metric space. Apply the defining finite-subcover property of compactness to the given indexed cover. The cover need not be countable. If $X=\varnothing$, choose $J=\varnothing$. Thus the assertion also includes empty and finite spaces.

**Lean declarations:** `exercise26`.

<a id="r02e27"></a>
### 2.27 — Condensation points and the countable remainder
**Lean source:** [Exercise27.lean](../../../Math/Rudin/Chapter02/Exercise27.lean).
**Inventory status:** Verified as stated.

**Statement.** For an uncountable set $E\subseteq\mathbb R^k$, define

$$
P=\{x:\text{every open neighborhood }U\text{ of }x\text{ meets }E\text{ uncountably}\}.
$$

Then $P$ is perfect and $E\setminus P$ is at most countable. A condensation point is not required to belong to $E$. The Lean results establish closedness and absence of isolated points for this $P$, and countability of the remainder, for every subset of any second-countable topological space, without assuming $E$ uncountable.

**Proof.** If $x\notin P$, some open neighborhood $U$ has $U\cap E$ at most countable. The same $U$ shows that every point of $U$ lies outside $P$. Thus $P$ is closed.

Choose a countable base $\mathcal B$. Each $x\in E\setminus P$ belongs to a base member $V$ contained in an open neighborhood whose intersection with $E$ is at most countable. Consequently

$$
E\setminus P\subseteq
\bigcup_{\substack{V\in\mathcal B\\V\cap E\text{ at most countable}}}(V\cap E).
$$

This is a countable union of at most countable sets, so the remainder is at most countable.

If $x\in P$ were isolated in $P$, an open neighborhood $U$ of $x$ would satisfy $U\cap P\subseteq\{x\}$. It would follow that $U\cap E\subseteq(E\setminus P)\cup\{x\}$ is at most countable, contrary to the definition of $P$. Thus $P$ is perfect. For the source's uncountable $E$, the countability of $E\setminus P$ also forces $P$ to be nonempty.

**Lean declarations:** `exercise27_perfect`, `exercise27_countable`.

<a id="r02e28"></a>
### 2.28 — Perfect-set decomposition and isolated points
**Lean source:** [Exercise28.lean](../../../Math/Rudin/Chapter02/Exercise28.lean).
**Inventory status:** Verified as stated.

**Statement.** Every closed subset $F$ of a separable metric space can be written

$$
F=P\cup C,
$$

where $P$ is perfect, possibly empty, and $C$ is at most countable. Every countably infinite closed subset of Euclidean $\mathbb R^k$ has an isolated point. More strongly, every nonempty at most countable closed subset of $\mathbb R^k$ has an isolated point. These Euclidean assertions allow $k=0$.

**Scope and countability convention.** Rudin uses “countable” to mean countably infinite in the source corollary. This already excludes the empty set, so the corollary is verified as stated, not refuted. If “countable” is instead translated as at most countable, nonemptiness must be stated. The empty set is closed and at most countable but has no isolated point because it has no member. This is a translation check, not a source erratum. The isolated-point corollary is not asserted for arbitrary separable metric spaces; for example, $\mathbb Q$ is closed in itself, countable, and has no isolated points.

**Proof.** A separable metric space is second countable. The Cantor–Bendixson decomposition theorem used in Lean gives the stated union. It can also be obtained from the condensation-point argument of Exercise 2.27: let $P$ be the condensation points of $F$. They form a perfect set and $F\setminus P$ is at most countable. Since $F$ is closed, every condensation point belongs to $F$; a point outside $F$ has the open neighborhood $X\setminus F$ meeting $F$ in no points. Thus $C=F\setminus P$ gives $F=P\cup C$. For $F=\varnothing$, take both parts empty.

Now let $F\subseteq\mathbb R^k$ be closed, nonempty, and at most countable. If no member were isolated, $F$ would be a nonempty perfect set. The perfect-set theorem in complete metric spaces supplies an injection of binary sequence space into $F$. Binary sequence space is uncountable by the diagonal argument, contradicting countability of $F$. Hence an isolated point exists. A countably infinite $F$ is nonempty, so the source corollary follows. The empty-set check follows directly from the impossibility of choosing $x\in\varnothing$.

**Lean declarations:** `exercise28_decomposition`, `exercise28_source`, `exercise28_empty`, `exercise28_nonempty`.

<a id="r02e29"></a>
### 2.29 — Disjoint open intervals, including unbounded components
**Lean source:** [Exercise29.lean](../../../Math/Rudin/Chapter02/Exercise29.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** Every open set $U\subseteq\mathbb R$ is the union of an at most countable family of pairwise disjoint nonempty open interval components. Each component has one of the forms

$$
(a,b)\quad(a<b),\qquad(a,\infty),\qquad(-\infty,b),\qquad\mathbb R,
$$

with finite real $a,b$ where applicable. The empty open set has the empty family. Each ray and the whole line has just itself as its component.

**Correction.** The source says “segments.” Definition 2.17 displays two finite real endpoints; under that bounded-only reading, the assertion is false. Later usage on book page 278 explicitly permits unbounded segments. The verified decomposition uses that extended open-interval convention. It does not silently replace finite endpoints by infinite endpoints. Separately, the Lean file proves that the connected open set $\mathbb R$ cannot be a pairwise disjoint union of bounded open segments, even without a countability restriction and even if empty segments are allowed.

**Proof.** For each $x\in U$, take its connected component $C_x$ within $U$, and retain distinct components only. Each component is nonempty and connected. It is open: every point $y$ in it has a small open interval contained in $U$; this interval is connected and meets the component, so maximality places the interval in the same component. Distinct components are disjoint, and every point of $U$ lies in its own component. Thus they cover $U$.

A connected subset of $\mathbb R$ contains every point between any two of its points. Hence each open nonempty component is an interval. If it is bounded on both sides, its infimum and supremum give $(a,b)$; if bounded on just one side, it is the corresponding open ray; if unbounded on both sides, it is $\mathbb R$. Endpoints cannot be included because the component is open. Each component contains a rational number. Choosing one rational in each gives an injection into $\mathbb Q$, because distinct components are disjoint. The family is therefore at most countable. If $U$ is empty there is no component to choose; if $U$ is a nonempty connected interval, ray, or the whole line, its only component is $U$.

For the bounded-only obstruction, suppose a pairwise disjoint family of bounded open segments covered $\mathbb R$. Choose a member $I$ containing $0$. The complement of $I$ is the union of all the other members, hence is open. Thus $I$ is a nonempty clopen subset of connected $\mathbb R$, so $I=\mathbb R$. But a bounded open segment omits its finite left endpoint and cannot be the whole line. This contradiction proves the refutation.

**Lean declarations:** `exercise29_source_segments`, `exercise29_bounded_segment_obstruction`, `exercise29_open_interval_decomposition`, `exercise29_components_empty`, `exercise29_components_Ioi`, `exercise29_components_Iio`, `exercise29_components_univ`.

<a id="r02e30"></a>
### 2.30 — Euclidean Baire theorem by nested compact balls
**Lean source:** [Exercise30.lean](../../../Math/Rudin/Chapter02/Exercise30.lean).
**Inventory status:** Verified as stated.

**Statement.** In $\mathbb R^k$:

1. If $\mathbb R^k=\bigcup_{n\ge1}F_n$ and every $F_n$ is closed, some $F_n$ has nonempty interior.
2. If every $G_n$ is open and dense, then $\bigcap_{n\ge1}G_n$ is nonempty.
3. The same intersection is dense.

The Lean statements allow every nonnegative integer $k$, including $k=0$. Their zero-based indices denote the source's positive indices.

**Proof.** Let $U$ be any nonempty open subset of $\mathbb R^k$. Choose a closed ball $K_0=\overline B(c_0,r_0)\subseteq U$ with $r_0>0$. Given $K_{n-1}=\overline B(c_{n-1},r_{n-1})$, density and openness of $G_n$ make

$$
B(c_{n-1},r_{n-1})\cap G_n
$$

nonempty and open. Choose a positive-radius closed ball $K_n$ inside this intersection. Thus each $K_n$ is nonempty and closed, $K_n\subseteq K_{n-1}$, and $K_n\subseteq G_n$.

Euclidean closed balls are compact. The nested compact-set theorem gives a point $x\in\bigcap_{n\ge0}K_n$. Then $x\in U$ and $x\in G_n$ for every $n\ge1$. Since every nonempty open $U$ meets $\bigcap_{n\ge1}G_n$, the intersection is dense. Taking $U=\mathbb R^k$, which contains the zero vector even when $k=0$, proves nonemptiness. No shrinking-radius assumption is needed: compactness of the first ball and nesting suffice.

Finally, if every closed $F_n$ in the cover had empty interior, each complement $G_n=\mathbb R^k\setminus F_n$ would be open and dense. The preceding construction would give a point in all these complements, outside the supposed cover. Therefore some $F_n$ has nonempty interior. This is the requested nested-set argument, not an invocation of Baire's theorem as a black box.

**Lean declarations:** `exercise30_closed_cover`, `exercise30_open_intersection_nonempty`, `exercise30_open_intersection_dense`.
