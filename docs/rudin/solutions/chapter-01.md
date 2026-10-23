<a id="chapter-01"></a>

# Chapter 1 — The Real and Complex Number Systems

[All chapters](../solutions.md) · [Next chapter](chapter-02.md)

**Exercises:** [1](#r01e01) · [2](#r01e02) · [3](#r01e03) · [4](#r01e04) · [5](#r01e05) · [6](#r01e06) · [7](#r01e07) · [8](#r01e08) · [9](#r01e09) · [10](#r01e10) · [11](#r01e11) · [12](#r01e12) · [13](#r01e13) · [14](#r01e14) · [15](#r01e15) · [16](#r01e16) · [17](#r01e17) · [18](#r01e18) · [19](#r01e19) · [20](#r01e20)

<a id="r01e01"></a>
### 1.1 — Rational operations preserve irrationality
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter01/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** If $r\in\mathbb Q\setminus\{0\}$ and $x\in\mathbb R$ is irrational, both $r+x$ and $rx$ are irrational.

**Proof.** If $r+x$ were rational, subtracting $r$ would make $x$ rational. If $rx$ were rational, division by the nonzero rational $r$ would make $x$ rational. Both conclusions contradict the hypothesis.

**Lean declarations:** `exercise01`.

<a id="r01e02"></a>
### 1.2 — No rational square root of twelve
**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter01/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** For every $q\in\mathbb Q$, $q^2\ne12$.

**Proof.** A natural number that is a rational square is an integer square. Indeed, if $q=a/b$ is in lowest terms with $b>0$, then $a^2=12b^2$ forces $b=1$, since $a^2$ and $b^2$ are relatively prime. But $3^2<12<4^2$, so $12$ is not an integer square. The Lean proof uses the standard rational-square criterion for natural numbers.

**Lean declarations:** `exercise02`.

<a id="r01e03"></a>
### 1.3 — Multiplicative consequences of the field axioms
**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter01/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** In any field, let $x\ne0$.

1. If $xy=xz$, then $y=z$.
2. If $xy=x$, then $y=1$.
3. If $xy=1$, then $y=1/x$.
4. $1/(1/x)=x$.

**Proof.** Multiplication of $xy=xz$ by $x^{-1}$ gives $y=z$. Apply this cancellation first to $xy=x\cdot1$, and then to $xy=x(1/x)=1$, to obtain the second and third claims. Finally, $1/x\ne0$ and $(1/x)x=1$, so the third claim applied to $1/x$ gives $x=1/(1/x)$.

**Lean declarations:** `exercise03_a`, `exercise03_b`, `exercise03_c`, `exercise03_d`.

<a id="r01e04"></a>
### 1.4 — Lower bounds precede upper bounds
**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter01/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be a nonempty subset of a linearly ordered set. If $\alpha$ is a lower bound of $E$ and $\beta$ is an upper bound, then $\alpha\le\beta$.

**Proof.** Choose $x\in E$. The bound assumptions give $\alpha\le x\le\beta$, and transitivity gives the result.

**Lean declarations:** `exercise04`.

<a id="r01e05"></a>
### 1.5 — Infimum by negation
**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter01/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** If $A\subseteq\mathbb R$ is nonempty and bounded below, then $-A=\{-a:a\in A\}$ is nonempty and bounded above, and

$$
\inf A=-\sup(-A).
$$

**Proof.** An element $a\in A$ gives $-a\in-A$. A lower bound $b$ of $A$ gives the upper bound $-b$ of $-A$. Write $s=\sup(-A)$. For each $a\in A$, $-a\le s$, hence $-s\le a$. Thus $-s$ is a lower bound of $A$. If $c$ is any lower bound, $-c$ bounds $-A$ above, so $s\le-c$ and $c\le-s$. Therefore $-s$ is the greatest lower bound.

**Lean declarations:** `exercise05`.

<a id="r01e06"></a>
### 1.6 — Powers constructed from roots and suprema
**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter01/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** Fix $b>1$.

1. For $a>0$ and an integer $n>0$, there is a unique positive $u$ satisfying $u^n=a$. If integers $m,n,p,q$ satisfy $n,q>0$ and $m/n=p/q$, the positive $n$th root of $b^m$ equals the positive $q$th root of $b^p$. Thus these roots define $b^r$ unambiguously for $r\in\mathbb Q$, with every fraction representation giving the same value.
2. For $r,s\in\mathbb Q$, $b^{r+s}=b^rb^s$.
3. For real $x$, put

   $$
   B(x)=\{b^t:t\in\mathbb Q,\ t\le x\}.
   $$

   This set is nonempty and bounded above. For rational $r$, $b^r=\sup B(r)$. Consequently $b^x:=\sup B(x)$ extends the rational definition.
4. For real $x,y$, these supremum-defined powers satisfy $b^{x+y}=b^xb^y$.

**Proof.** To distinguish the construction from the library power function, write $P_b(x)$ for the standard real power. The standard laws for positive bases give

$$
P_a(1/n)>0,\qquad P_a(1/n)^n=a.
$$

If $u>0$ and $u^n=a$, raising both sides to the power $1/n$ gives $u=P_a(1/n)$. Thus the root selected by its defining equation exists, is unique, and equals this standard power. In particular, the positive $n$th root of $b^m$ is $P_b(m/n)$. Equal fractions therefore give equal roots, even when their numerators are negative. The standard addition law now gives the rational addition law.

Choose a rational $t<x$ to see that $B(x)$ is nonempty. Monotonicity gives $b^t=P_b(t)\le P_b(x)$ whenever $t\le x$, so $B(x)$ is bounded above. If $x=r$ is rational, $b^r$ belongs to $B(r)$ and bounds it above; it is therefore its maximum and supremum.

For arbitrary real $x$, let $S=\sup B(x)$. We already have $S\le P_b(x)$. If $z<P_b(x)$, continuity of $P_b$ gives a neighborhood of $x$ on which $P_b(t)>z$. Rational density supplies a rational $t<x$ in that neighborhood. Then $z<b^t\le S$. This proves $S=P_b(x)$. The standard addition law for $P_b$ now proves the addition law for the constructed real powers.

**Scope.** The roots and suprema are the actual definitions in the file. Their agreement with standard real powers is proved, not assumed as a definition. The condition in $B(x)$ is $t\le x$, including its endpoint.

**Lean declarations:** `exercise06_a`, `exercise06_root_exists`, `exercise06_root_spec`, `exercise06_rationalPower_fraction`, `exercise06_b`, `exercise06_c_supremum`, `exercise06_lowerPowers_nonempty`, `exercise06_lowerPowers_bddAbove`, `exercise06_realPower_eq_rpow`, `exercise06_c_real_power`, `exercise06_d`.

<a id="r01e07"></a>
### 1.7 — A logarithm obtained from a supremum
**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter01/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** Fix $b>1$ and use the powers constructed in Exercise 1.6. For each $y>0$, there is exactly one real $x$ such that $b^x=y$. The construction has these seven steps:

1. $b^n-1\ge n(b-1)$ for each positive integer $n$; the formal result also includes $n=0$.
2. $b-1\ge n(b^{1/n}-1)$ for each positive integer $n$.
3. If $t>1$ and the positive integer $n$ satisfies $n>(b-1)/(t-1)$, then $b^{1/n}<t$.
4. If $b^w<y$, then $b^{w+1/n}<y$ for every sufficiently large positive integer $n$.
5. If $b^w>y$, then $b^{w-1/n}>y$ for every sufficiently large positive integer $n$.
6. $A=\{w\in\mathbb R:b^w<y\}$ is nonempty and bounded above, and $x=\sup A$ satisfies $b^x=y$.
7. Any two solutions coincide.

**Proof.** Bernoulli's inequality, applied to $b=1+(b-1)$, gives (1). Apply (1) with base $b^{1/n}>1$ and use $(b^{1/n})^n=b$ to get (2). Under the hypothesis of (3),

$$
n(b^{1/n}-1)\le b-1<n(t-1),
$$

which gives $b^{1/n}<t$.

For (4), set $t=y/b^w>1$. Choose an integer threshold $N\ge1$ larger than $(b-1)/(t-1)$. For every $n\ge N$, part (3) and the addition law give $b^{w+1/n}=b^wb^{1/n}<y$. For (5), use $t=b^w/y>1$ instead. Then $b^{1/n}<b^w/y$ and hence $b^{w-1/n}=b^w/b^{1/n}>y$ for all sufficiently large $n$.

The powers $b^n$ are unbounded, for example by (1). Choose $n$ with $b^n>1/y$; then $-n\in A$. Choose $m$ with $b^m>y$. Strict monotonicity of powers shows that every $w\in A$ satisfies $w<m$, so $A$ is bounded above.

Let $x=\sup A$. If $b^x<y$, part (4) gives $x+1/N\in A$ for some $N>0$, contrary to $x$ being an upper bound. If $b^x>y$, part (5) gives $b^{x-1/N}>y$. Every $w\in A$ then satisfies $w<x-1/N$, so $x-1/N$ is an upper bound smaller than $x$. Both alternatives are impossible, proving $b^x=y$. Finally, strict monotonicity makes $x\mapsto b^x$ injective, proving uniqueness.

**Lean declarations:** `exercise07_a`, `exercise07_b`, `exercise07_c`, `exercise07_d`, `exercise07_e`, `exercise07_A_nonempty`, `exercise07_A_bddAbove`, `exercise07_f`, `exercise07_g`, `exercise07`.

<a id="r01e08"></a>
### 1.8 — The complex field cannot be ordered
**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter01/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** No linear order on $\mathbb C$ makes its usual field operations into an ordered field.

**Proof.** In an ordered field every square is nonnegative. Thus $i^2=-1$ would be nonnegative. But the ordered-field axioms give $0<1$, hence $-1<0$, a contradiction. This excludes every proposed linear order, not merely a particular one.

**Lean declarations:** `exercise08`.

<a id="r01e09"></a>
### 1.9 — Lexicographic order lacks least upper bounds
**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter01/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** Define

$$
a+bi<c+di\quad\Longleftrightarrow\quad a<c\ \text{or}\ (a=c\ \text{and}\ b<d).
$$

This is a strict linear order on $\mathbb C$, but it does not have the least-upper-bound property. The imaginary axis $E=\{z:\operatorname{Re}z=0\}$ is a counterexample: its upper bounds are exactly the numbers with positive real part.

**Proof.** Irreflexivity follows from irreflexivity of the real order. For transitivity, if either comparison increases the real coordinate, the composite comparison does too; otherwise all three real coordinates agree and transitivity holds in the imaginary coordinates. Comparing real coordinates, and then imaginary coordinates when necessary, gives trichotomy.

If $\operatorname{Re}u>0$, every point of $E$ precedes $u$. Conversely, an upper bound $u$ must dominate $i(\operatorname{Im}u+1)$. Since its imaginary coordinate is too small for the equal-real-coordinate alternative, $\operatorname{Re}u>0$. The set $E$ contains $0$ and is bounded above by $1$. For any upper bound $u$, the number $u-i$ is a strictly smaller upper bound with the same positive real part. Thus no least upper bound exists.

**Lean declarations:** `exercise09_lt_iff`, `exercise09_linear_order`, `exercise09_upperBounds`, `exercise09_no_lub`.

<a id="r01e10"></a>
### 1.10 — Explicit complex square roots
**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter01/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** For $w=u+iv\in\mathbb C$, set

$$
a=\sqrt{\frac{|w|+u}{2}},\qquad b=\sqrt{\frac{|w|-u}{2}},\qquad z=a+bi.
$$

Both coefficients are nonnegative. If $v\ge0$, then $z^2=w$; if $v\le0$, then $\overline z^{\,2}=w$. Let $\rho=z$ when $v\ge0$, and $\rho=\overline z$ otherwise. For $w\ne0$, the square roots are exactly the two distinct numbers $\rho$ and $-\rho$. For $w=0$, the unique square root is $0$.

**Proof.** Since $|u|\le|w|$, the radicands are nonnegative. Their squares give $a^2-b^2=u$. Also,

$$
(2ab)^2=4a^2b^2=|w|^2-u^2=v^2.
$$

Both $2ab$ and $|v|$ are nonnegative, so $2ab=|v|$. Therefore $z^2=u+i|v|$ and $\overline z^{\,2}=u-i|v|$, proving both sign-dependent formulas, including $v=0$.

For any $t$, the equation $t^2=w=\rho^2$ factors as $(t-\rho)(t+\rho)=0$. Thus $t=\rho$ or $t=-\rho$. If $w\ne0$, then $\rho\ne0$, so these roots are distinct. If $w=0$, the equation $t^2=0$ implies $t=0$.

**Lean declarations:** `exercise10_nonnegative_imaginary`, `exercise10_nonpositive_imaginary`, `exercise10_nonzero_roots`, `exercise10_zero_root`.

<a id="r01e11"></a>
### 1.11 — Radius and unit factor
**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter01/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Every $z\in\mathbb C$ has a representation $z=rw$ with $r\ge0$ and $|w|=1$. The radius is always uniquely determined as $r=|z|$. The unit factor is unique exactly when $z\ne0$. For $z=0$, all representations have $r=0$ and arbitrary $w$ of modulus one.

**Proof.** For $z\ne0$, take $r=|z|$ and $w=z/|z|$. Then $|w|=1$ and $rw=z$. For $z=0$, take $r=0,w=1$. In any admissible representation, $|z|=|r||w|=r$, which proves radius uniqueness. When $z\ne0$, division by this positive radius forces $w=z/|z|$. When $z=0$, the radius must vanish, and every unit $w$ works. In particular, the distinct choices $1$ and $-1$ show that the unit factor is not unique.

**Lean declarations:** `exercise11`, `exercise11_radius_uniqueness`, `exercise11_unit_uniqueness`, `exercise11_unit_unique_iff`, `exercise11_zero_choices`.

<a id="r01e12"></a>
### 1.12 — The finite triangle inequality
**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter01/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** For complex numbers $z_1,\ldots,z_n$,

$$
\left|\sum_{j=1}^n z_j\right|\le\sum_{j=1}^n|z_j|.
$$

The formal result permits every $n\ge0$, including the empty sum.

**Proof.** The empty case is $0\le0$. If the result holds for $n$, the triangle inequality gives

$$
\left|\sum_{j=1}^{n+1}z_j\right|\le\left|\sum_{j=1}^nz_j\right|+|z_{n+1}|\le\sum_{j=1}^{n+1}|z_j|.
$$

Induction proves the claim.

**Lean declarations:** `exercise12`.

<a id="r01e13"></a>
### 1.13 — The reverse triangle inequality
**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter01/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** For $x,y\in\mathbb C$,

$$
\bigl||x|-|y|\bigr|\le|x-y|.
$$

**Proof.** From $x=(x-y)+y$, the triangle inequality gives $|x|-|y|\le|x-y|$. Interchanging $x,y$ gives $|y|-|x|\le|y-x|=|x-y|$. Together these inequalities bound the absolute value of the difference.

**Lean declarations:** `exercise13`.

<a id="r01e14"></a>
### 1.14 — A sum of squared moduli
**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter01/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** If $z\in\mathbb C$ and $|z|=1$, then $|1+z|^2+|1-z|^2=4$.

**Proof.** The parallelogram identity gives

$$
|1+z|^2+|1-z|^2=2|1|^2+2|z|^2=4.
$$

**Lean declarations:** `exercise14`.

<a id="r01e15"></a>
### 1.15 — Equality in finite complex Schwarz inequality
**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter01/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** For $a,b\in\mathbb C^n$,

$$
\left|\sum_{j=1}^na_j\overline{b_j}\right|^2\le
\left(\sum_{j=1}^n|a_j|^2\right)\left(\sum_{j=1}^n|b_j|^2\right).
$$

Equality holds exactly when $a=0$, or $b=0$, or $b=ca$ for some nonzero $c\in\mathbb C$. Equivalently, equality holds if and only if $a=0$ or $b=ca$ for some scalar $c$. This includes $n=0$ and both zero-vector cases.

**Proof.** Give $\mathbb C^n$ its Euclidean norm and use the convention

$$
\langle b,a\rangle=\sum_j a_j\overline{b_j},\qquad \|a\|^2=\sum_j|a_j|^2.
$$

Cauchy–Schwarz gives $|\langle b,a\rangle|\le\|a\|\|b\|$; squaring gives the displayed inequality. The standard inner-product equality theorem states that equality holds precisely when $a=0$ or $b=ca$ for some scalar $c$. It applies also to the squared equality because both unsquared sides are nonnegative. If the scalar is zero, then $b=0$; otherwise it gives the stated nonzero-scalar branch. Conversely each of these three branches gives equality, by direct substitution or by the same equality theorem.

**Lean declarations:** `exercise15`, `exercise15_inner_sum`, `exercise15_norm_sq_sum`, `exercise15_schwarz`.

<a id="r01e16"></a>
### 1.16 — Intersections of equal-radius spheres
**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter01/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $x,y\in\mathbb R^k$ satisfy $d=\|x-y\|>0$, and let $r>0$. The number of points $z$ such that $\|z-x\|=\|z-y\|=r$ is:

| Dimension | $2r>d$ | $2r=d$ | $2r<d$ |
| --- | --- | --- | --- |
| $k\ge3$ | Infinitely many | One | None |
| $k=2$ | Two | One | None |
| $k=1$ | None | One | None |

More generally, for any dimension and $r\ge0$, with $m=(x+y)/2$,

$$
\|z-x\|=\|z-y\|=r
\quad\Longleftrightarrow\quad
\langle y-x,z-m\rangle=0,\qquad
\|z-m\|^2=r^2-\frac{\|y-x\|^2}{4}.
$$

If $s\ge0$ and $s^2=r^2-\|y-x\|^2/4$, the locus is exactly the image of the radius-$s$ sphere in $(\mathbb R(y-x))^\perp$ under $u\mapsto m+u$.

**Proof.** Write $u=z-m$ and $v=(y-x)/2$. Then $z-x=u+v$ and $z-y=u-v$, so expansion gives

$$
\|z-x\|^2=\|u\|^2+\frac{d^2}{4}+\langle y-x,u\rangle,
$$

$$
\|z-y\|^2=\|u\|^2+\frac{d^2}{4}-\langle y-x,u\rangle.
$$

Adding and subtracting proves the equivalence; the reverse implication uses nonnegativity to pass from squared norms to norms. It also proves the asserted sphere-image description.

If $2r<d$, the triangle inequality would give $d\le\|x-z\|+\|z-y\|=2r$, a contradiction. Under $r>0$, the squared radius $r^2-d^2/4$ is negative in this case, so it cannot be the square of a real norm. No square-root construction is valid for this branch. If $2r=d$, the squared radius is zero, forcing $z=m$, which does satisfy both equations.

Suppose $2r>d$. Since $x\ne y$, the perpendicular subspace has dimension $k-1$, and $s=\sqrt{r^2-d^2/4}>0$. For $k=1$, that subspace is $\{0\}$, so it has no vector of norm $s$. For $k=2$, it is a line; its radius-$s$ sphere consists of two opposite vectors. Translation preserves their distinctness. For $k\ge3$, its dimension is at least two. A positive-radius sphere in such a space is connected and contains two distinct opposite points; a connected finite subset of a metric space is a singleton, so this sphere is infinite. Its translation is injective and therefore has infinite image.

**Scope.** The bridge and tangency theorem also allow $r=0$ and coincident centers in every dimension. The no-intersection theorem needs only $2r<\|x-y\|$. The dimension-dependent counts above retain the source assumptions $d>0$ and $r>0$.

**Lean declarations:** `exercise16_a`, `exercise16_bridge`, `exercise16_sphere_image`, `exercise16_b`, `exercise16_c`, `exercise16_dimension_two`, `exercise16_dimension_one_cases`.

<a id="r01e17"></a>
### 1.17 — The parallelogram identity and its geometry
**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter01/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** For $x,y\in\mathbb R^k$,

$$
\|x+y\|^2+\|x-y\|^2=2\|x\|^2+2\|y\|^2.
$$

If four vertices $a,b,c,d$ in order satisfy $a+c=b+d$, then

$$
\|a-c\|^2+\|b-d\|^2=
\|a-b\|^2+\|b-c\|^2+\|c-d\|^2+\|d-a\|^2.
$$

Thus the sum of the squared diagonal lengths equals the sum of the squared side lengths, including degenerate parallelograms.

**Proof.** Expand each squared norm using the inner product. The cross terms $2\langle x,y\rangle$ and $-2\langle x,y\rangle$ cancel. For the geometric version, set $x=b-a$ and $y=d-a$. The relation on vertices gives $c=a+x+y$. The diagonal vectors are $x+y$ and $x-y$, up to sign, and the side lengths are $\|x\|,\|y\|,\|x\|,\|y\|$. Substitution gives the formula without any nondegeneracy assumption.

**Lean declarations:** `exercise17`, `exercise17_geometry`.

<a id="r01e18"></a>
### 1.18 — A nonzero orthogonal vector
**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter01/Exercise18.lean).
**Inventory status:** Verified as stated.

**Statement.** For $k\ge2$ and every $x\in\mathbb R^k$, there is a nonzero $y\in\mathbb R^k$ with $x\cdot y=0$. In dimension one, such a $y$ exists exactly when $x=0$.

**Proof.** If $x_1=x_2=0$, take $y=e_1$. Otherwise take

$$
y=x_1e_2-x_2e_1.
$$

At least one of its first two coordinates is nonzero, and $x\cdot y=-x_1x_2+x_2x_1=0$. In dimension one, orthogonality is $xy=0$. If $y\ne0$, this forces $x=0$. Conversely, $x=0$ is orthogonal to the nonzero vector $1$.

**Lean declarations:** `exercise18`, `exercise18_vector_spec`, `exercise18_dimension_one`.

<a id="r01e19"></a>
### 1.19 — A distance locus and its zero-radius exception
**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter01/Exercise19.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** The printed request asks, for arbitrary $a,b\in\mathbb R^k$, for a center $c$ and radius $r>0$ such that

$$
\|x-a\|=2\|x-b\|\quad\Longleftrightarrow\quad\|x-c\|=r
$$

for every $x$, with $3c=4b-a$ and $3r=2\|b-a\|$.

**Correction.** The unrestricted positive-radius claim is false when $a=b$. The valid construction in every dimension, including dimension zero, is

$$
c=\frac{4b-a}{3},\qquad r=\frac{2\|b-a\|}{3}\ge0.
$$

It gives the stated equivalence for every $x$. If $a\ne b$, then $r>0$. If $a=b$, the locus is exactly $\{a\}$, with $c=a,r=0$, and it cannot equal a positive-radius sphere about any center.

**Proof.** Expanding squared Euclidean norms gives

$$
\|x-a\|^2-4\|x-b\|^2=-3\bigl(\|x-c\|^2-r^2\bigr).
$$

Thus the two squared distance equations are equivalent. All distances and $r$ are nonnegative, so the unsquared equations are equivalent as well. When $a\ne b$, $\|b-a\|>0$, proving positivity.

When $a=b$, the equation $\|x-a\|=2\|x-a\|$ forces $x=a$. Suppose this singleton were a sphere with center $c$ and radius $r>0$. Since $a$ lies on it, its reflection $2c-a$ also lies on it, because $\|(2c-a)-c\|=\|a-c\|$. The singleton condition forces $2c-a=a$, hence $c=a$, which would give $r=0$, a contradiction. In particular, $a=b=0$ in $\mathbb R^1$ is an explicit counterexample to the original universal claim.

**Lean declarations:** `exercise19`, `exercise19_original_counterexample`, `exercise19_nondegenerate`, `exercise19_degenerate_no_positive_radius`, `exercise19_degenerate`.

<a id="r01e20"></a>
### 1.20 — Dedekind cuts with greatest elements allowed
**Lean source:** [Exercise20.lean](../../../Math/Rudin/Chapter01/Exercise20.lean).
**Inventory status:** Verified as stated.

**Statement.** Let a modified cut be a nonempty proper subset $A\subset\mathbb Q$ such that $p\in A$ and $q<p$ imply $q\in A$. Greatest elements are allowed. Order these cuts by strict inclusion, and define addition by the exact set of pairwise sums:

$$
A+B=\{r+s:r\in A,\ s\in B\}.
$$

These cuts are linearly ordered and have the least-upper-bound property. Addition satisfies A1–A4: closure, commutativity, associativity, and an additive identity. The identity is $Z=\{q\in\mathbb Q:q\le0\}$, which has greatest element $0$. A5 fails: the cut $N=\{q\in\mathbb Q:q<0\}$ has no additive inverse relative to $Z$.

**Proof.** First, if $r\in A$ and $s\notin A$, then $r<s$, since otherwise downward closure would imply $s\in A$. If $A\not\subseteq B$, choose $r\in A\setminus B$. Every $s\in B$ satisfies $s<r$, so $s\in A$. Hence $B\subseteq A$. Inclusion is reflexive, antisymmetric, and transitive; this comparability gives a linear order and trichotomy for strict inclusion.

Let $\mathcal A$ be a nonempty family of cuts bounded above by a cut $B$. Its union $U=\bigcup_{A\in\mathcal A}A$ is nonempty and downward closed. It is contained in $B$, so it is proper. Every member of $\mathcal A$ is contained in $U$, and every upper bound of the family contains $U$. Thus $U$ is its least upper bound, with membership exactly $q\in U$ if and only if $q\in A$ for some $A\in\mathcal A$.

For closure under addition, choose elements of $A$ and $B$ to obtain an element of $A+B$. Choose $r'\notin A$ and $s'\notin B$. Every sum $r+s\in A+B$ satisfies $r+s<r'+s'$, so $r'+s'\notin A+B$ and the sum is proper. If $q\le r+s$, then $q-s\le r$, so $q-s\in A$ and $q=(q-s)+s\in A+B$. Thus it is a modified cut; no extra closure points are added.

Commutativity follows from $r+s=s+r$. Associativity follows because both $(A+B)+C$ and $A+(B+C)$ consist exactly of the sums $r+s+t$ with $r\in A,s\in B,t\in C$. For the identity, $r\in A$ and $s\le0$ imply $r+s\in A$, while each $r\in A$ equals $r+0$. Hence $A+Z=A$, and commutativity gives $Z+A=A$.

Finally, suppose $N+B=Z$. Since $0\in Z$, there are $r<0$ and $s\in B$ with $r+s=0$. But $r/2<0$, so $r/2+s\in N+B$. This number equals $-r/2>0$, contradicting membership in $Z$. Thus $N$ has no inverse, and the universal inverse axiom fails.

**Lean declarations:** `exercise20_order`, `exercise20_cut_properties`, `exercise20_least_upper_bounds`, `exercise20_union_isLUB`, `exercise20_addition_closed`, `exercise20_mem_add`, `exercise20_addition_commutative`, `exercise20_addition_associative`, `exercise20_zero`, `exercise20_zero_has_greatest`, `exercise20_inverse_failure`, `exercise20_not_A5`.
