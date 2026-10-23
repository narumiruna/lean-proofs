<a id="chapter-03"></a>

# Chapter 3 — Numerical Sequences and Series

[All chapters](../solutions.md) · [Previous chapter](chapter-02.md) · [Next chapter](chapter-04.md)

**Exercises:** [1](#r03e01) · [2](#r03e02) · [3](#r03e03) · [4](#r03e04) · [5](#r03e05) · [6](#r03e06) · [7](#r03e07) · [8](#r03e08) · [9](#r03e09) · [10](#r03e10) · [11](#r03e11) · [12](#r03e12) · [13](#r03e13) · [14](#r03e14) · [15](#r03e15) · [16](#r03e16) · [17](#r03e17) · [18](#r03e18) · [19](#r03e19) · [20](#r03e20) · [21](#r03e21) · [22](#r03e22) · [23](#r03e23) · [24](#r03e24) · [25](#r03e25)

<a id="r03e01"></a>
### 3.1 — Limits of absolute values
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter03/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** If a real or complex sequence $s_n$ tends to $s$, then $|s_n|\to|s|$. The converse is false. More generally, convergence in a seminormed additive group implies convergence of the norms.

**Proof.** The reverse triangle inequality gives

$$
\bigl|\|s_n\|-\|s\|\bigr|\leq\|s_n-s\|\longrightarrow0.
$$

For the converse, take $s_n=(-1)^n$. Its absolute values are all $1$, but its even and odd subsequences have the distinct limits $1$ and $-1$. Thus it has no limit.

**Lean declarations:** `exercise01_absolute_values`, `exercise01_converse`.

<a id="r03e02"></a>
### 3.2 — A square-root difference
**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter03/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** As positive integers $n$ tend to infinity,

$$
\sqrt{n^2+n}-n\longrightarrow\frac12.
$$

**Proof.** For $x>0$, rationalization gives

$$
\sqrt{x^2+x}-x=\frac{x}{\sqrt{x^2+x}+x}
=\frac1{\sqrt{1+1/x}+1}.
$$

With $x=n$, the denominator tends to $2$, which is nonzero. The quotient therefore tends to $1/2$. The value at index zero does not affect this limit.

**Lean declarations:** `exercise02_limit`.

<a id="r03e03"></a>
### 3.3 — Convergence of nested radicals
**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter03/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** Define $s_1=\sqrt2$ and

$$
s_{n+1}=\sqrt{2+\sqrt{s_n}}\qquad(n\geq1).
$$

Then $0\leq s_n<2$ for every $n$, and $(s_n)$ converges.

**Proof.** The initial bound holds because $0\leq\sqrt2<2$. If $0\leq s_n<2$, then $\sqrt{s_n}<2$, so $0\leq s_{n+1}<\sqrt4=2$. This proves the bound by induction. Also $s_2\geq s_1$, and the update $t\mapsto\sqrt{2+\sqrt t}$ is increasing for $t\geq0$. Induction therefore gives $s_{n+1}\geq s_n$ for all $n$. A bounded increasing real sequence converges.

**Scope.** The inner square root is part of the source recurrence; the update is not $\sqrt{2+s_n}$. Lean uses index zero for $s_1$.

**Lean declarations:** `exercise03_convergence`, `exercise03_strict_bound`.

<a id="r03e04"></a>
### 3.4 — Upper and lower limits of a parity recurrence
**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter03/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $s_1=0$ and, for $m\geq1$, let

$$
s_{2m}=\frac{s_{2m-1}}2,\qquad s_{2m+1}=\frac12+s_{2m}.
$$

Then $\limsup s_n=1$ and $\liminf s_n=1/2$.

**Proof.** Induction using the two recurrence rules gives, for $m\geq0$,

$$
s_{2m+1}=1-2^{-m},\qquad s_{2m+2}=\frac{1-2^{-m}}2.
$$

Consequently the odd terms tend to $1$ and the even terms tend to $1/2$. Every term is between $0$ and $1$. Moreover, both parity formulas are eventually at least $1/2-\varepsilon$, for each $\varepsilon>0$. Thus the upper limit is at most $1$ and the lower limit is at least $1/2$. The two subsequence limits give the reverse inequalities.

**Lean declarations:** `exercise04_limsup`, `exercise04_liminf`.

<a id="r03e05"></a>
### 3.5 — Upper limit of a sum
**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter03/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** For real sequences $(a_n)$ and $(b_n)$, put $A=\limsup a_n$ and $B=\limsup b_n$ in the extended real line. If neither $(A,B)=(-\infty,+\infty)$ nor $(A,B)=(+\infty,-\infty)$, then

$$
\limsup(a_n+b_n)\leq A+B.
$$

**Proof.** If $A,B$ are finite, then eventually $a_n\leq A+\varepsilon$ and $b_n\leq B+\varepsilon$. Hence the upper limit of the sum is at most $A+B+2\varepsilon$; let $\varepsilon\downarrow0$. If an upper limit is $+\infty$, the exclusions make the right side $+\infty$, so the inequality is automatic. The remaining infinite case has one upper limit $-\infty$ and the other finite or $-\infty$. The latter sequence is eventually bounded above by a fixed real number, while the former is eventually below any chosen real number. Their sum tends to $-\infty$. This is the extended-real upper-limit inequality used in Lean.

**Lean declarations:** `exercise05_limsup_sum`.

<a id="r03e06"></a>
### 3.6 — Four series and the complex parameter domain
**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter03/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** All series below start at $n=1$.

1. $\sum(\sqrt{n+1}-\sqrt n)$ diverges to $+\infty$.
2. $\sum(\sqrt{n+1}-\sqrt n)/n$ converges absolutely.
3. $\sum(n^{1/n}-1)^n$ converges absolutely.
4. For $z\in\mathbb C$, $\sum1/(1+z^n)$ is defined precisely when $z^n\ne-1$ for every positive integer $n$. The excluded parameters are exactly roots of unity of even order. On the defined domain, the series converges if and only if $|z|>1$, and in that case it converges absolutely. It diverges for defined parameters with $|z|\leq1$.

**Proof.** In (1), the first $N$ terms sum to $\sqrt{N+1}-1$, which tends to $+\infty$.

For (2), rationalization gives

$$
0\leq\frac{\sqrt{n+1}-\sqrt n}{n}
=\frac1{n(\sqrt{n+1}+\sqrt n)}\leq\frac1{n^{3/2}}.
$$

The comparison series converges.

For (3), the standard limit $n^{1/n}\to1$ implies that eventually $|n^{1/n}-1|\leq1/2$. Hence the absolute value of the $n$th term is at most $2^{-n}$.

For (4), a denominator vanishes exactly when $z^n=-1$. Such a parameter satisfies $z^{2n}=1$ and $z^n\ne1$. Conversely, these two conditions imply $(z^n-1)(z^n+1)=0$ and therefore $z^n=-1$. Equivalently, its order as a root of unity is even: an even order gives $-1$ at its half-period, while an odd order cannot admit a power equal to $-1$.

If $|z|>1$, no power can equal $-1$, since $|z^n|>1$. Eventually $|z|^n\geq2$, and

$$
|1+z^n|\geq |z|^n-1\geq\tfrac12|z|^n,
\qquad \left|\frac1{1+z^n}\right|\leq2|z|^{-n}.
$$

Geometric comparison proves absolute convergence. If $|z|<1$, the terms tend to $1$, not zero. If $|z|=1$ and the denominators are nonzero, then $|1+z^n|\leq2$, so every term has modulus at least $1/2$. In both cases ordinary convergence fails by the term test. In fact, the same lower bound applies to all defined parameters with $|z|\leq1$.

**Scope.** A parameter with a zero denominator makes the source expression undefined; it is not classified as a divergent series. No value is assigned to division by zero.

**Lean declarations:** `exercise06_a`, `exercise06_b`, `exercise06_c`, `exercise06_d_defined_parameters`, `exercise06_d_undefined_even`, `exercise06_d_convergence`, `exercise06_d_absolute`.

<a id="r03e07"></a>
### 3.7 — A weighted square-root series
**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter03/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** If $a_n\geq0$ for $n\geq1$ and $\sum a_n$ converges, then $\sum\sqrt{a_n}/n$ converges.

**Proof.** The inequality $(\sqrt{a_n}-1/n)^2\geq0$ gives

$$
0\leq\frac{\sqrt{a_n}}n\leq\frac12\left(a_n+\frac1{n^2}\right).
$$

The right-hand series converges. Comparison proves convergence of the nonnegative series in the statement. The hypothesis requires only convergence of the ordinary partial sums; nonnegativity justifies the summability comparison.

**Lean declarations:** `exercise07_weighted_roots`.

<a id="r03e08"></a>
### 3.8 — A bounded monotone multiplier
**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter03/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $\sum a_n$ is a convergent complex series and $(b_n)$ is a bounded real sequence that is either nondecreasing or nonincreasing. Then $\sum a_nb_n$ converges. Absolute convergence of $\sum a_n$ is not required.

**Proof.** Bounded monotonicity gives a finite limit $b_n\to\ell$. The partial sums of $\sum a_n$ are bounded. The sequence $c_n=b_n-\ell$ is monotone and tends to zero. Dirichlet's test, obtained by summation by parts, gives convergence of $\sum c_na_n$; if $c_n$ is nondecreasing, apply the usual decreasing version to $-c_n$. Finally,

$$
\sum_{n<N}a_nb_n=\sum_{n<N}c_na_n+\ell\sum_{n<N}a_n,
$$

and both terms on the right converge. This is Abel's convergence test for ordinary, possibly conditional, series.

**Lean declarations:** `exercise08_monotone_multiplier`.

<a id="r03e09"></a>
### 3.9 — Four radii of convergence
**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter03/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** The complex power series

$$
\sum_{n\geq0}n^3z^n,\qquad
\sum_{n\geq0}\frac{2^n}{n!}z^n,\qquad
\sum_{n\geq1}\frac{2^n}{n^2}z^n,\qquad
\sum_{n\geq0}\frac{n^3}{3^n}z^n
$$

have radii of convergence $1$, $+\infty$, $1/2$, and $3$, respectively.

**Proof.** The ratios of consecutive nonzero coefficients tend, respectively, to

$$
\left(\frac{n+1}{n}\right)^3\to1,\qquad
\frac2{n+1}\to0,\qquad
2\left(\frac n{n+1}\right)^2\to2,\qquad
\frac13\left(\frac{n+1}{n}\right)^3\to\frac13.
$$

The coefficient ratio theorem gives the reciprocal of each positive limit as the radius, and infinite radius when the limit is zero. Finite initial coefficients do not affect the radius; the third series is extended by a zero constant coefficient in Lean. No boundary convergence classification is needed for these radius claims.

**Lean declarations:** `exercise09_a`, `exercise09_b`, `exercise09_c`, `exercise09_d`.

<a id="r03e10"></a>
### 3.10 — Integer coefficients restrict the radius
**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter03/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** If a complex power series $\sum a_nz^n$ has integer coefficients and infinitely many nonzero coefficients, its radius of convergence $R$ satisfies $R\leq1$.

**Proof.** If $R>1$, the series converges absolutely at $z=1$. In particular, $|a_n|\to0$. Eventually $|a_n|<1$, but an integer of absolute value less than $1$ is zero. This would leave only finitely many nonzero coefficients, a contradiction.

**Lean declarations:** `exercise10_integer_radius`.

<a id="r03e11"></a>
### 3.11 — Transformations of a positive divergent series
**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter03/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a_n>0$ for $n\geq1$, suppose $\sum a_n$ diverges, and put $s_n=\sum_{j=1}^n a_j$, with $s_0=0$.

1. $\sum a_n/(1+a_n)$ diverges.
2. For positive integers $N,k$,

   $$
   \sum_{j=1}^k\frac{a_{N+j}}{s_{N+j}}\geq1-\frac{s_N}{s_{N+k}}.
   $$

   Consequently $\sum a_n/s_n$ diverges.
3. For $n\geq2$,

   $$
   \frac{a_n}{s_n^2}\leq\frac1{s_{n-1}}-\frac1{s_n}.
   $$

   The series $\sum_{n\geq1}a_n/s_n^2$ converges.
4. The assumptions do not decide convergence of $\sum a_n/(1+na_n)$: both convergence and divergence occur. In contrast, $\sum a_n/(1+n^2a_n)$ always converges.

**Proof.** For (1), suppose the transformed series converges. Its terms tend to zero, so eventually $a_n/(1+a_n)\leq1/2$, which implies $a_n\leq1$. On this tail,

$$
a_n\leq2\frac{a_n}{1+a_n}.
$$

Comparison would make $\sum a_n$ converge, a contradiction.

For (2), $s_{N+j}\leq s_{N+k}$, and therefore

$$
\sum_{j=1}^k\frac{a_{N+j}}{s_{N+j}}
\geq\frac{s_{N+k}-s_N}{s_{N+k}}.
$$

Since the original terms are positive and their sum diverges, $s_n\to+\infty$. For each fixed $N$, the right side tends to $1$ as $k\to\infty$. Thus tails of the transformed series cannot be arbitrarily small, contrary to the Cauchy criterion for convergence.

For (3), all denominators below are positive when $n\geq2$, and

$$
\frac1{s_{n-1}}-\frac1{s_n}
=\frac{a_n}{s_{n-1}s_n}\geq\frac{a_n}{s_n^2}.
$$

The comparison telescopes. Its partial sums from $2$ to $N$ are at most $1/s_1$. Adding the finite first term $a_1/s_1^2=1/a_1$ proves convergence. This part in fact requires only positivity, not divergence of the original series.

For the divergent example in (4), take $a_n=1$. The original series diverges and the linear transform is $\sum1/(n+1)$, which also diverges. For a convergent example, take

$$
a_n=\frac1{(n+1)^2}+\mathbf1_{\{2^j:j\geq0\}}(n).
$$

These terms are strictly positive and are at least $1$ at every power of two, so their series diverges. Away from powers of two, the linear transform is at most $(n+1)^{-2}$; at $n=2^j$ it is at most $1/n=2^{-j}$. Both comparison sums converge. Finally, for every positive sequence,

$$
0<\frac{a_n}{1+n^2a_n}\leq\frac1{n^2},
$$

which proves the quadratic-denominator assertion without a divergence hypothesis.

**Scope.** The reciprocal inequality in (3) is not asserted at $n=1$, where $s_0=0$.

**Lean declarations:** `exercise11_a`, `exercise11_b_inequality`, `exercise11_b_divergence`, `exercise11_c_inequality`, `exercise11_c_convergence`, `exercise11_d_linear_classification`, `exercise11_d_linear_convergent_example`, `exercise11_d_linear_divergent_example`, `exercise11_d_quadratic`.

<a id="r03e12"></a>
### 3.12 — Transformations using positive tails
**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter03/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a_n>0$ for $n\geq1$, suppose $\sum a_n$ converges, and set $r_n=\sum_{j=n}^{\infty}a_j$.

1. For positive integers $m<n$,

   $$
   \sum_{j=m}^n\frac{a_j}{r_j}>1-\frac{r_n}{r_m}.
   $$

   The series $\sum a_n/r_n$ diverges.
2. For every $n\geq1$,

   $$
   \frac{a_n}{\sqrt{r_n}}<2(\sqrt{r_n}-\sqrt{r_{n+1}}).
   $$

   The series $\sum a_n/\sqrt{r_n}$ converges.

**Proof.** The tails satisfy $r_n>r_{n+1}>0$, $r_n-r_{n+1}=a_n$, and $r_n\to0$. For (1), use $r_j\leq r_m$ when $j\geq m$:

$$
\sum_{j=m}^n\frac{a_j}{r_j}
\geq\frac{r_m-r_{n+1}}{r_m}
>\frac{r_m-r_n}{r_m}.
$$

For each fixed $m$, the last expression tends to $1$ as $n\to\infty$. A convergent transformed series would therefore have every infinite tail at least $1$, whereas its tails must tend to zero. This contradiction proves divergence.

For (2), put $x=\sqrt{r_n}$ and $y=\sqrt{r_{n+1}}$. Then $0<y<x$ and

$$
\frac{a_n}{\sqrt{r_n}}=\frac{x^2-y^2}{x}
=(x-y)\left(1+\frac yx\right)<2(x-y).
$$

Summing this bound telescopes and bounds all partial sums by $2\sqrt{r_1}$. Since the terms are positive, the series converges.

**Lean declarations:** `exercise12_a_inequality`, `exercise12_a_divergence`, `exercise12_b_inequality`, `exercise12_b_convergence`.

<a id="r03e13"></a>
### 3.13 — Absolute convergence of a Cauchy product
**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter03/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $\sum_{n\geq0}a_n$ and $\sum_{n\geq0}b_n$ be absolutely convergent complex series. Their Cauchy product, with coefficients

$$
c_n=\sum_{k=0}^n a_kb_{n-k},
$$

is absolutely convergent.

**Proof.** Write $A=\sum|a_n|$ and $B=\sum|b_n|$. The triangle inequality and nonnegativity give, for each $N$,

$$
\sum_{n=0}^N|c_n|
\leq\sum_{\substack{k,j\geq0\\k+j\leq N}}|a_k||b_j|
\leq AB.
$$

Thus the increasing partial sums of $\sum|c_n|$ are bounded and converge. This is the standard absolute Cauchy-product theorem used in Lean. Both hypotheses refer to ordered partial sums of absolute values, not to an assumed unconditional interpretation of a conditionally convergent series.

**Lean declarations:** `exercise13_absolute_cauchy_product`.

<a id="r03e14"></a>
### 3.14 — Arithmetic means and Tauberian converses
**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter03/Exercise14.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** For a complex sequence $(s_n)_{n\geq0}$ define

$$
\sigma_n=\frac1{n+1}\sum_{k=0}^n s_k,\qquad a_n=s_n-s_{n-1}\quad(n\geq1).
$$

1. If $s_n\to s$, then $\sigma_n\to s$.
2. The converse fails: a nonconvergent sequence can have $\sigma_n\to0$.
3. This can occur even with every $s_n$ a positive real number and $\limsup s_n=+\infty$.
4. For $n\geq1$,

   $$
   s_n-\sigma_n=\frac1{n+1}\sum_{k=1}^n k a_k.
   $$

   If $na_n\to0$ and $\sigma_n\to\sigma$, then $s_n\to\sigma$.
5. The same conclusion holds under the weaker hypothesis that there is a finite real $M$ with $|ka_k|\leq M$ for every $k\geq1$. For $0\leq m<n$ the prescribed identity is

   $$
   s_n-\sigma_n=\frac{m+1}{n-m}(\sigma_n-\sigma_m)
      +\frac1{n-m}\sum_{i=m+1}^n(s_n-s_i).
   $$

   For $m<i\leq n$, the bounds used in the proof are

   $$
   |s_n-s_i|\leq\frac{(n-i)M}{i+1}\leq\frac{(n-m-1)M}{m+2}.
   $$

   With the floor choice specified below, the corrected final bound is $|s_n-s_i|\leq M\varepsilon$. It is strict if $M>0$.

**Correction.** The source prints $|s_n-s_i|<M\varepsilon$ while allowing $M=0$. The zero sequence satisfies all bound and mean-convergence assumptions with $M=0$, but the strict bound would be $0<0$. This refutes only that intermediate strict estimate. The non-strict correction proves the unchanged final converse without strengthening its hypotheses.

**Proof.** For (1), fix $\varepsilon>0$ and choose $K$ such that $|s_k-s|<\varepsilon$ for $k\geq K$. For $n\geq K$,

$$
|\sigma_n-s|\leq\frac1{n+1}\sum_{k<K}|s_k-s|+\varepsilon.
$$

The finite first sum divided by $n+1$ tends to zero, proving the arithmetic-mean theorem.

For (2) and (3), use the construction proved in the source file. Put

$$
F(n)=\lfloor n^{1/4}\rfloor^2,\qquad
s_n=F(n)-F(n-1)+\frac1{n+1},
$$

where $F(-1)$ is interpreted as $F(0)=0$ for the term at $n=0$. The function $F$ is nondecreasing, so $s_n>0$. At $n=(k+1)^4$, the jump in $F$ is $2k+1$, so $s_{(k+1)^4}\geq2k+1$ and $\limsup s_n=+\infty$. On the other hand, telescoping yields

$$
\sigma_n=\frac{F(n)}{n+1}+\frac1{n+1}\sum_{k=0}^n\frac1{k+1}.
$$

The first term tends to zero since $F(n)\leq\sqrt n$. The second tends to zero by (1), applied to $1/(k+1)$. This positive real sequence, also regarded as complex, proves both assertions and cannot have a finite limit.

For (4), expand and telescope the weighted differences:

$$
\sum_{k=1}^n k(s_k-s_{k-1})=(n+1)s_n-\sum_{k=0}^n s_k.
$$

This is the claimed identity. When $ka_k\to0$, its arithmetic means tend to zero by (1), and hence $s_n-\sigma_n\to0$.

For (5), subtract the two identities defining $(n+1)\sigma_n$ and $(m+1)\sigma_m$, and expand the sum of $s_n-s_i$. Rearrangement gives the stated block identity. The bound on $|ka_k|$ implies $M\geq0$. Since

$$
s_n-s_i=\sum_{k=i+1}^n a_k,\qquad |a_k|\leq\frac Mk\leq\frac M{i+1},
$$

the first estimate follows by the triangle inequality. The second follows from $i\geq m+1$, which bounds the numerator above by $(n-m-1)M$ and the denominator below by $m+2$.

Fix $\varepsilon>0$. For $n\geq\varepsilon$, choose

$$
m=\left\lfloor\frac{n-\varepsilon}{1+\varepsilon}\right\rfloor.
$$

The floor inequalities give

$$
0\leq m<n,\qquad
m\leq\frac{n-\varepsilon}{1+\varepsilon}<m+1,\qquad
\frac{m+1}{n-m}\leq\frac1\varepsilon,\qquad
\frac{n-m-1}{m+2}<\varepsilon.
$$

Indeed, the lower floor bound gives $\varepsilon(m+1)\leq n-m$, and the upper bound gives $n-m-1<\varepsilon(m+2)$. Thus $|s_n-s_i|\leq M\varepsilon$ for $m<i\leq n$, with strict inequality when $M>0$. For $M=0$, the zero-sequence obstruction applies at every $n\geq1$ with $\varepsilon=1$ and this same floor index; in particular $i=n$ is permitted.

Taking norms in the block identity and using its $n-m$ summands gives

$$
|s_n-\sigma|\leq\frac1\varepsilon|\sigma_n-\sigma_m|
+M\varepsilon+|\sigma_n-\sigma|.
$$

For fixed $\varepsilon$, this choice of $m$ tends to infinity with $n$. If $\sigma_n\to\sigma$, the right side tends to $M\varepsilon$. Therefore, in the extended real sense,

$$
\limsup_{n\to\infty}|s_n-\sigma|\leq M\varepsilon
$$

for every $\varepsilon>0$. Letting $\varepsilon\downarrow0$ and using nonnegativity proves $s_n\to\sigma$, including the case $M=0$.

**Lean declarations:** `exercise14_a`, `exercise14_b`, `exercise14_c`, `exercise14_d_identity`, `exercise14_d_convergence`, `exercise14_e_identity`, `exercise14_e_estimate`, `exercise14_e_index_choice`, `exercise14_e_index_estimate`, `exercise14_e_limsup`, `exercise14_e_convergence`, `exercise14_e_zero_bound_obstruction`, `exercise14_e_index_estimate_strict`.

<a id="r03e15"></a>
### 3.15 — Series in Euclidean space
**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter03/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** Fix a positive integer $k$ and use the Euclidean norm on $\mathbb R^k$. Series convergence means convergence of the ordered partial sums $S_N=\sum_{n=0}^{N-1}a_n$. The following extensions of the scalar series theorems hold.

1. **Cauchy criterion (3.22).** The series converges if and only if for every $\varepsilon>0$ there is $N$ such that

   $$
   \left\|\sum_{j=n}^m a_j\right\|\leq\varepsilon\qquad(m\geq n\geq N).
   $$

2. **Term test (3.23).** Convergence implies $a_n\to0$.
3. **Comparison (3.25(a)).** If a real series $\sum c_n$ converges and $\|a_n\|\leq c_n$ eventually, then $\sum a_n$ converges.
4. **Root test (3.33).** Put $L=\limsup_{n\to\infty}\|a_n\|^{1/n}$, using $n\geq1$ and extended nonnegative values. If $L<1$, the series converges; if $L>1$, it diverges. The case $L=1$ does not decide convergence.
5. **Ratio test (3.34).** Assume $a_n\ne0$ eventually, so the norm ratios are defined on a tail. If $\limsup\|a_{n+1}\|/\|a_n\|<1$, the series converges. If these ratios are at least $1$ eventually, it diverges.
6. **Dirichlet test (3.42).** If $(S_N)$ is bounded and the real sequence $b_n$ is nonincreasing with limit zero, then $\sum b_na_n$ converges.
7. **Absolute convergence (3.45).** If $\sum\|a_n\|$ converges, then $\sum a_n$ converges.
8. **Linearity (3.47).** If $\sum a_n=A$ and $\sum b_n=B$, then $\sum(a_n+b_n)=A+B$. For each fixed real $c$, $\sum ca_n=cA$.
9. **Rearrangements (3.55).** Every rearrangement by a permutation of the natural numbers of an absolutely convergent vector series converges to the original sum.

**Proof.** For (1), an inclusive tail is $S_{m+1}-S_n$. Thus convergence implies the displayed condition. Conversely, apply the condition with tolerance $\varepsilon/2$ to see that the partial sums form a Cauchy sequence. Completeness of $\mathbb R^k$ gives a limit. For (2), $a_n=S_{n+1}-S_n\to0$.

For (3), discard the finite initial segment on which the comparison need not hold. On the remaining tail $c_n\geq0$, and

$$
\left\|\sum_{j=n}^m a_j\right\|\leq\sum_{j=n}^m\|a_j\|\leq\sum_{j=n}^m c_j.
$$

The scalar Cauchy criterion and (1) give convergence. Taking $c_n=\|a_n\|$ also proves (7).

For (4), if $L<1$, choose $q$ with $L<q<1$. Eventually $\|a_n\|^{1/n}\leq q$, so $\|a_n\|\leq q^n$ and geometric comparison applies. If a series converges, then eventually $\|a_n\|<1$, so its upper root limit is at most $1$. This proves divergence when $L>1$, including $L=+\infty$. For the boundary case choose a unit vector $v$: the series with $a_0=0$ and $a_n=n^{-2}v$ for $n\geq1$ converges, while the constant terms $b_n=v$ give a divergent series. Both upper root limits equal $1$, since $n^{-2/n}\to1$.

For (5), choose a number $q<1$ above the upper ratio limit. The eventual estimate $\|a_{n+1}\|\leq q\|a_n\|$ gives a geometric bound by induction. In the divergence case, the norms on a sufficiently late tail are nondecreasing and bounded below by a positive initial norm. They cannot tend to zero.

For (6), write $a_n=S_{n+1}-S_n$ and use summation by parts. If $\|S_j\|\leq M$, then for $m\geq n$,

$$
\sum_{j=n}^m b_ja_j
=b_mS_{m+1}-b_nS_n+\sum_{j=n+1}^m(b_{j-1}-b_j)S_j.
$$

Since a nonincreasing sequence tending to zero is nonnegative, the norm of this tail is at most $2Mb_n$, which tends to zero. The Cauchy criterion applies.

For (8), finite sums distribute over addition and scalar multiplication; continuity of these operations gives the asserted limits. For (9), choose a finite initial set outside which the sum of norms is small. Every sufficiently long rearranged partial sum contains that set, and its difference from the full sum is bounded by the remaining sum of norms. Thus its limit is unchanged.

**Scope.** No absolute-convergence assumption is added to the Cauchy criterion, term test, Dirichlet test, or linearity statements. Ratios are ratios of norms, not vector quotients, and zero denominators are excluded eventually. The file also handles $k=0$: every term is the zero vector, every series converges, and the upper root limit is $0$. The root-test boundary examples require $k>0$.

**Lean declarations:** `exercise15_cauchy_criterion`, `exercise15_terms_tend_zero`, `exercise15_comparison`, `exercise15_root_convergence`, `exercise15_root_divergence`, `exercise15_root_boundary`, `exercise15_dimension_zero`, `exercise15_ratio_convergence`, `exercise15_ratio_divergence`, `exercise15_dirichlet`, `exercise15_absolute_implies_convergent`, `exercise15_addition`, `exercise15_scalar_multiplication`, `exercise15_rearrangements`.

<a id="r03e16"></a>
### 3.16 — Newton iteration for a square root
**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter03/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $\alpha>0$, let $x_1>\sqrt\alpha$, and define

$$
x_{n+1}=\frac12\left(x_n+\frac\alpha{x_n}\right).
$$

Then $x_n>\sqrt\alpha$ for all $n$, the sequence is strictly decreasing, and $x_n\to\sqrt\alpha$. For $\varepsilon_n=x_n-\sqrt\alpha$ and $\beta=2\sqrt\alpha$,

$$
\varepsilon_{n+1}=\frac{\varepsilon_n^2}{2x_n}
<\frac{\varepsilon_n^2}{\beta},\qquad
\varepsilon_{n+1}<\beta\left(\frac{\varepsilon_1}{\beta}\right)^{2^n}\quad(n\geq1).
$$

When $\alpha=3$ and $x_1=2$,

$$
\frac{\varepsilon_1}{\beta}<\frac1{10},\qquad
\varepsilon_5<4\cdot10^{-16},\qquad
\varepsilon_6<4\cdot10^{-32}.
$$

**Proof.** Put $r=\sqrt\alpha>0$. For $x>r$, direct algebra gives

$$
\frac{x+\alpha/x}{2}-r=\frac{(x-r)^2}{2x}>0.
$$

Also $\alpha/x<x$, so the update is strictly less than $x$. Induction proves positivity of all denominators, the strict lower bound, and strict decrease. Thus $x_n\to L\geq r>0$. Passing to the limit in the recurrence gives $L=(L+\alpha/L)/2$, hence $L^2=\alpha$ and $L=r$.

The displayed algebra is the exact error identity. Since $x_n>r$ and $\varepsilon_n>0$, replacing $2x_n$ by $\beta$ makes the quotient strictly larger. Dividing by $\beta$ gives $\varepsilon_{n+1}/\beta<(\varepsilon_n/\beta)^2$; induction gives the iterated error estimate. No assumption that $\varepsilon_1/\beta<1$ is needed for that inequality or for convergence already proved.

For the numerical case, $\sqrt3>5/3$ implies

$$
\frac{2-\sqrt3}{2\sqrt3}<\frac1{10},
$$

and $2\sqrt3<4$. Apply the general estimate with $n=4$ and $n=5$ to obtain the fifth- and sixth-term bounds.

**Lean declarations:** `exercise16_monotone`, `exercise16_limit`, `exercise16_error_step`, `exercise16_error_bound`, `exercise16_initial_bound`, `exercise16_fifth_bound`, `exercise16_sixth_bound`.

<a id="r03e17"></a>
### 3.17 — Alternating square-root iteration and its rate
**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter03/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $\alpha>1$ and $x_1>\sqrt\alpha$. Define

$$
x_{n+1}=\frac{\alpha+x_n}{1+x_n}
=x_n+\frac{\alpha-x_n^2}{1+x_n}.
$$

Then

$$
x_1>x_3>x_5>\cdots>\sqrt\alpha,\qquad
x_2<x_4<x_6<\cdots<\sqrt\alpha,
$$

and the full sequence tends to $\sqrt\alpha$. Writing $r=\sqrt\alpha$, its successive-error ratios satisfy

$$
\frac{x_{n+1}-r}{x_n-r}\longrightarrow\frac{1-r}{1+r},\qquad
\frac{|x_{n+1}-r|}{|x_n-r|}\longrightarrow\frac{r-1}{r+1}\in(0,1).
$$

Thus convergence is linear. For the Newton sequence $(y_n)$ of Exercise 3.16, under its hypotheses $\alpha>0$ and $y_1>r$,

$$
\frac{y_{n+1}-r}{y_n-r}\to0,\qquad
\frac{y_{n+1}-r}{(y_n-r)^2}\to\frac1{2r},
$$

so that method has quadratic convergence.

**Proof.** All iterates are positive. With $f(y)=(\alpha+y)/(1+y)$,

$$
f(y)-r=\frac{(1-r)(y-r)}{1+y}.
$$

Since $r>1$, each step changes the sign of the nonzero error. Moreover,

$$
f(f(y))-y=\frac{2(\alpha-y^2)}{\alpha+1+2y}.
$$

The denominator is positive. This difference is negative above $r$ and positive below $r$, proving the strict odd and even monotonicity.

For convergence, define $t_n=(x_n-r)/(x_n+r)$. Algebra gives

$$
t_n=\left(\frac{1-r}{1+r}\right)^{n-1}\frac{x_1-r}{x_1+r}.
$$

The multiplier has absolute value less than $1$, so $t_n\to0$. Since $x_n=r(1+t_n)/(1-t_n)$, it follows that $x_n\to r$. Dividing the error identity by $x_n-r\ne0$ gives the signed ratio $(1-r)/(1+x_n)$ and therefore its stated limit; taking absolute values gives the positive rate.

For Newton's method, the exact error identity from Exercise 3.16 gives the two ratios

$$
\frac{y_n-r}{2y_n},\qquad\frac1{2y_n}.
$$

Because $y_n\to r>0$, their limits are $0$ and $1/(2r)$, respectively.

**Lean declarations:** `exercise17_odd_decreasing`, `exercise17_even_increasing`, `exercise17_limit`, `exercise17_rate`, `exercise17_absolute_rate`, `exercise17_newton_comparison`, `exercise17_newton_quadratic_rate`.

<a id="r03e18"></a>
### 3.18 — Newton iteration for positive integer roots
**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter03/Exercise18.lean).
**Inventory status:** Verified as stated.

**Statement.** Retain $\alpha>0$ and $x_1>\sqrt\alpha$ from Exercise 3.16. For a positive integer $p$, replace its update by

$$
x_{n+1}=N(x_n),\qquad
N(x)=\frac{p-1}{p}x+\frac\alpha p x^{1-p}
=\frac{(p-1)x+\alpha/x^{p-1}}p.
$$

Every iterate is positive, and all powers and denominators in this real formula are defined.

1. If $p=1$, then $x_n=\alpha$ for every $n\geq2$; the limit is reached after one update.
2. If $p\geq2$, let $r=\alpha^{1/p}$ be the unique positive root of $r^p=\alpha$. Then $x_n\to r$, with three cases:
   - If $x_1<r$, the first step increases past $r$: $x_1<r<x_2$. From $x_2$ onward the sequence is strictly decreasing and stays above $r$.
   - If $x_1=r$, every term equals $r$.
   - If $x_1>r$, the entire sequence is strictly decreasing and stays above $r$.

**Proof.** The inherited initial bound implies $x_1>0$. For $p\geq1$ and $x>0$, the numerator of $N(x)$ is positive: $(p-1)x\geq0$ and $\alpha/x^{p-1}>0$. Thus positivity follows by induction, $p\ne0$, and $x_n^{p-1}\ne0$. On this domain the integer power $x^{1-p}$ is exactly the reciprocal of $x^{p-1}$. For $p=1$, the formula reduces to $N(x)=\alpha$.

Now suppose $p\geq2$. The positive real power $r=\alpha^{1/p}$ has $r^p=\alpha$, and strict monotonicity of $t\mapsto t^p$ on positive reals gives uniqueness. Direct algebra yields

$$
N(x)-x=\frac{r^p-x^p}{p x^{p-1}}.
$$

Also $N(r)=r$. For $x>0$ with $x\ne r$, the strict Bernoulli inequality applied to $r/x>0$ gives

$$
\left(\frac rx\right)^p>1+p\left(\frac rx-1\right),
$$

so

$$
N(x)-r=\frac xp\left[\left(\frac rx\right)^p-1-p\left(\frac rx-1\right)\right]>0.
$$

Thus every non-root positive start maps strictly above $r$. The difference formula then proves all the stated directions of motion and the constant case.

For $x\geq r$, one has $r^p/x^{p-1}\leq r$, and hence

$$
0\leq N(x)-r\leq\frac{p-1}{p}(x-r).
$$

The factor lies in $[0,1)$. Iteration bounds the errors by a geometric sequence and proves convergence for a start above $r$. A start below $r$ is covered after its first step. This bound proves convergence but does not assert an exact asymptotic order.

**Scope.** The starting hypothesis is not silently replaced by $x_1>\alpha^{1/p}$. The classification is proved for every positive start and then specialized to the inherited bound. That bound really allows the below-root case: for $\alpha=1/64$, $p=3$, and $x_1=3/16$,

$$
\sqrt\alpha=\frac18<\frac3{16}<\frac14=r<x_2.
$$

The formula concerns the positive real branch only; $p=0$, nonpositive starts, and other real or complex roots are outside the stated domain.

**Lean declarations:** `exercise18_well_defined`, `exercise18_source_update`, `exercise18_unit_exponent`, `exercise18_unit_limit`, `exercise18_higher_exponents`, `exercise18_below_example`.

<a id="r03e19"></a>
### 3.19 — Ternary series and the Cantor set
**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter03/Exercise19.lean).
**Inventory status:** Verified as stated.

**Statement.** The middle-thirds Cantor set is exactly

$$
\left\{\sum_{n=1}^{\infty}\frac{\alpha_n}{3^n}:\alpha_n\in\{0,2\}\text{ for every }n\right\}.
$$

Every displayed series converges, and every Cantor-set point, including endpoints, has such a representation.

**Proof.** The terms are nonnegative and at most $2/3^n$, so geometric comparison proves convergence. For a prescribed sequence of digits let $t_m=\sum_{n=1}^m\alpha_n/3^n$. The remaining tail lies in $[0,3^{-m}]$. The interval $[t_m,t_m+3^{-m}]$ is one of the closed intervals retained at stage $m$ of the middle-thirds construction: a digit $0$ chooses the left third, and a digit $2$ chooses the right third. The series sum therefore lies in every stage and hence in the Cantor set.

Conversely, if $x$ belongs to the Cantor set, at each stage choose the retained third containing $x$, consistently inside the preceding chosen interval. These choices give digits $\alpha_n\in\{0,2\}$ and intervals $[t_m,t_m+3^{-m}]$ containing $x$. Thus $|x-t_m|\leq3^{-m}\to0$, proving the representation. Closed intervals retain their endpoints, so this argument includes $0$, $1$, and all deleted-interval endpoints. It does not require a unique unrestricted ternary expansion; for example $1/3=\sum_{n=2}^{\infty}2/3^n$. Lean uses the standard ternary characterization of the literal middle-thirds construction.

**Lean declarations:** `exercise19_digits_in_cantor`, `exercise19_cantor_has_digits`, `exercise19_image`.

<a id="r03e20"></a>
### 3.20 — A convergent subsequence of a Cauchy sequence
**Lean source:** [Exercise20.lean](../../../Math/Rudin/Chapter03/Exercise20.lean).
**Inventory status:** Verified as stated.

**Statement.** In any metric space $X$, let $(p_n)$ be Cauchy and let $\varphi:\mathbb N\to\mathbb N$ be strictly increasing. If $p_{\varphi(j)}\to p\in X$, then $p_n\to p$. Completeness of $X$ is not assumed.

**Proof.** Given $\varepsilon>0$, choose $N$ such that $d(p_n,p_m)<\varepsilon/2$ for $m,n\geq N$. Since $\varphi(j)\to\infty$, choose $j$ with $\varphi(j)\geq N$ and $d(p_{\varphi(j)},p)<\varepsilon/2$. Then for every $n\geq N$,

$$
d(p_n,p)\leq d(p_n,p_{\varphi(j)})+d(p_{\varphi(j)},p)<\varepsilon.
$$

**Lean declarations:** `exercise20_full_convergence`.

<a id="r03e21"></a>
### 3.21 — Nested sets with vanishing diameter
**Lean source:** [Exercise21.lean](../../../Math/Rudin/Chapter03/Exercise21.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X$ be a complete metric space, and let $E_n$ be nonempty closed bounded subsets with $E_{n+1}\subseteq E_n$ and $\operatorname{diam}(E_n)\to0$. Then $\bigcap_nE_n$ consists of exactly one point. Uniqueness alone requires only boundedness of each $E_n$ and vanishing diameter, not completeness, closedness, nonemptiness, or nesting.

**Proof.** Choose $x_n\in E_n$. If $m,n\geq N$, nesting puts both points in $E_N$, so

$$
d(x_m,x_n)\leq\operatorname{diam}(E_N).
$$

Thus $(x_n)$ is Cauchy and has a limit $x\in X$. For each fixed $N$, its tail lies in the closed set $E_N$, so $x\in E_N$. This proves nonemptiness of the intersection. If $x,y$ both lie in every $E_n$, boundedness gives $d(x,y)\leq\operatorname{diam}(E_n)$ for all $n$. Passing to the limit gives $d(x,y)=0$, so $x=y$. The last argument establishes the stated weaker hypotheses for uniqueness.

**Lean declarations:** `exercise21_intersection_exists`, `exercise21_intersection_unique`, `exercise21_singleton`.

<a id="r03e22"></a>
### 3.22 — Baire's theorem
**Lean source:** [Exercise22.lean](../../../Math/Rudin/Chapter03/Exercise22.lean).
**Inventory status:** Verified as stated.

**Statement.** If $X$ is a nonempty complete metric space and each $G_n$ is open and dense in $X$, then $\bigcap_nG_n$ is nonempty and dense. Density itself holds without the nonempty-space assumption.

**Proof.** This is Baire's theorem for complete metric spaces, as used in Lean. To see the nested-set argument, start with any nonempty open set $U$. Density and openness allow a nonempty closed ball $B_1$ of positive radius inside $U\cap G_1$. Inductively choose a nonempty closed ball $B_{n+1}$ inside the open ball with the same center and radius as $B_n$, intersected with $G_{n+1}$, and give it radius at most $2^{-(n+1)}$. This is possible because that intersection is nonempty and open. Choose the first radius at most $1/2$ as well. The balls are nested, closed, bounded, and have diameters tending to zero. Exercise 3.21 supplies a common point. It belongs to $U$ and every $G_n$. Thus every nonempty open set meets the intersection, proving density. If $X$ is nonempty, take $U=X$ to obtain nonemptiness. If $X$ is empty, density is vacuous but nonemptiness is not asserted.

**Lean declarations:** `exercise22_baire_nonempty`, `exercise22_baire_dense`.

<a id="r03e23"></a>
### 3.23 — Limits of distances between Cauchy sequences
**Lean source:** [Exercise23.lean](../../../Math/Rudin/Chapter03/Exercise23.lean).
**Inventory status:** Verified as stated.

**Statement.** If $(p_n)$ and $(q_n)$ are Cauchy sequences in any metric space $X$, then $d(p_n,q_n)$ has a finite real limit. The space $X$ need not be complete.

**Proof.** Two applications of the triangle inequality give

$$
|d(p_n,q_n)-d(p_m,q_m)|\leq d(p_n,p_m)+d(q_n,q_m).
$$

Both terms on the right are uniformly small for sufficiently large $m,n$. Thus the real distance sequence is Cauchy, and completeness of $\mathbb R$ gives a finite limit. The Lean proof expresses the same fact through uniform continuity of the distance function.

**Lean declarations:** `exercise23_distance_limit`.

<a id="r03e24"></a>
### 3.24 — Completion by classes of Cauchy sequences
**Lean source:** [Exercise24.lean](../../../Math/Rudin/Chapter03/Exercise24.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X$ be any metric space, with no nonemptiness assumption. On its Cauchy sequences define

$$
(p_n)\sim(q_n)\quad\Longleftrightarrow\quad d(p_n,q_n)\to0.
$$

1. This is an equivalence relation.
2. On the quotient $X^*$, the formula

   $$
   \Delta([(p_n)],[(q_n)])=\lim_{n\to\infty}d(p_n,q_n)
   $$

   is well defined and is a metric.
3. The metric space $X^*$ is complete.
4. The map $\varphi:X\to X^*$ sending $p$ to the class of the constant sequence $p,p,\ldots$ is an isometric embedding:

   $$
   \Delta(\varphi(p),\varphi(q))=d(p,q).
   $$

5. Its image is dense in $X^*$. If $X$ is complete, $\varphi$ is surjective, so $\varphi(X)=X^*$.

**Proof.** Reflexivity and symmetry in (1) follow from the corresponding metric axioms. If $p\sim q$ and $q\sim r$, then

$$
0\leq d(p_n,r_n)\leq d(p_n,q_n)+d(q_n,r_n)\to0,
$$

which proves transitivity.

By Exercise 3.23, the real limit defining $\Delta$ exists for every pair of Cauchy sequences. If $p\sim p'$ and $q\sim q'$, then

$$
|d(p_n,q_n)-d(p'_n,q'_n)|\leq d(p_n,p'_n)+d(q_n,q'_n)\to0.
$$

Thus the limit is independent of both representatives. Nonnegativity, symmetry, and the triangle inequality pass to limits. Self-distance is zero, and $\Delta(P,Q)=0$ holds exactly when their representatives are equivalent, that is, exactly when $P=Q$. This proves every metric axiom in (2).

For (3), the Lean construction identifies this actual sequence quotient with the standard complete metric completion $\widehat X$; it does not replace the quotient definition. Let $\iota:X\to\widehat X$ be the standard dense isometric embedding. Every Cauchy sequence $(p_n)$ has a limit $\widehat p$ after applying $\iota$. Continuity of distance gives

$$
\lim_n d(p_n,q_n)=d(\widehat p,\widehat q).
$$

Consequently two sequences are equivalent exactly when these limits in $\widehat X$ agree. The map $[(p_n)]\mapsto\widehat p$ is therefore well defined and injective, and it preserves the metric already specified by $\Delta$. It is surjective: density of $\iota(X)$ gives, for each $z\in\widehat X$, a sequence $\iota(p_n)\to z$. The sequence $(p_n)$ is Cauchy because $\iota$ preserves distances, and its class maps to $z$. Hence the quotient is isometric to the complete space $\widehat X$ and is complete. These are the standard completion and sequential-closure results used by the Lean proof.

For (4), the distance between two constant sequences is constantly $d(p,q)$. Taking its limit proves the identity and hence injectivity.

For (5), if $P=[(p_n)]$, then $\varphi(p_n)\to P$. Indeed, given $\varepsilon>0$, Cauchyness gives $N$ such that $d(p_n,p_m)<\varepsilon/2$ for $m,n\geq N$. For fixed $n\geq N$, taking $m\to\infty$ yields $\Delta(\varphi(p_n),P)\leq\varepsilon/2<\varepsilon$. Thus every class lies in the closure of the image. If $X$ is complete, a representative $(p_n)$ converges to some $p\in X$, so it is equivalent to the constant sequence at $p$. Every class is then $\varphi(p)$.

**Scope.** If $X$ is empty, there are no sequences $\mathbb N\to X$, so $X^*$ is empty. It is still a complete metric space, the embedding has dense image, and the asserted surjectivity is valid. No arbitrary point of $X$ is assumed in the construction.

**Lean declarations:** `exercise24_a`, `sequence_distance_limit`, `exercise24_b_well_defined`, `dist_eq_delta`, `distance_limit`, `exercise24_b_metric`, `exercise24_c`, `exercise24_d_embedding`, `exercise24_d`, `embed_injective`, `exercise24_e_density`, `exercise24_e_surjective`, `exercise24_e_range`.

<a id="r03e25"></a>
### 3.25 — The completion of the rational numbers
**Lean source:** [Exercise25.lean](../../../Math/Rudin/Chapter03/Exercise25.lean).
**Inventory status:** Verified as stated.

**Statement.** For the rational metric $d(p,q)=|p-q|$, the sequence-quotient completion $\mathbb Q^*$ from Exercise 3.24 is isometric to $\mathbb R$. There is an isometric bijection $T:\mathbb Q^*\to\mathbb R$ such that

$$
T(\varphi(q))=q\quad(q\in\mathbb Q),\qquad
\Delta(P,Q)=|T(P)-T(Q)|.
$$

For every rational Cauchy sequence $(q_n)$, its ordinary real limit is $T([(q_n)])$. The domain is complete and the image of the original rationals is dense in $\mathbb R$.

**Proof.** The usual inclusion $\mathbb Q\hookrightarrow\mathbb R$ preserves the stated distance. Every rational Cauchy sequence therefore has a real limit. Define $T([(q_n)])=\lim_n q_n$. Equivalent representatives have the same limit, and continuity of absolute value gives

$$
\Delta([(p_n)],[(q_n)])=\lim_n|p_n-q_n|
=|T([(p_n)])-T([(q_n)])|.
$$

Thus $T$ is an isometry and is injective. A constant rational sequence has its rational value as real limit, proving compatibility with $\varphi$ and the representative-limit assertion.

By Exercise 3.24 the domain is complete. The image of a complete space under an isometry into a metric space is closed. Here the image contains every rational number, and the rationals are dense in $\mathbb R$, so that closed image is all of $\mathbb R$. Hence $T$ is surjective and gives the required isometric identification. Its values on $\varphi(\mathbb Q)$ are precisely the ordinary rational points, whose density proves the last claim.

**Lean declarations:** `exercise25_identification`, `exercise25_distance`, `exercise25_representative_limit`, `exercise25_rational_completion_embed`, `exercise25_completeness_density`.
