<a id="chapter-09"></a>

# Chapter 9 — Functions of Several Variables

[All chapters](../solutions.md) · [Previous chapter](chapter-08.md) · [Next chapter](chapter-10.md)

**Exercises:** [1](#r09e01) · [2](#r09e02) · [3](#r09e03) · [4](#r09e04) · [5](#r09e05) · [6](#r09e06) · [7](#r09e07) · [8](#r09e08) · [9](#r09e09) · [10](#r09e10) · [11](#r09e11) · [12](#r09e12) · [13](#r09e13) · [14](#r09e14) · [15](#r09e15) · [16](#r09e16) · [17](#r09e17) · [18](#r09e18) · [19](#r09e19) · [20](#r09e20) · [21](#r09e21) · [22](#r09e22) · [23](#r09e23) · [24](#r09e24) · [25](#r09e25) · [26](#r09e26) · [27](#r09e27) · [28](#r09e28) · [29](#r09e29) · [30](#r09e30) · [31](#r09e31)

<a id="r09e01"></a>
### 9.1 — Finite linear combinations form a vector space
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter09/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X$ be a real vector space and $S\subseteq X$ nonempty. The set of finite linear combinations of elements of $S$ is a vector subspace of $X$, with the inherited operations. The formal result applies more generally to a vector space over any field $K$.

**Proof.** Define

$$
V=\left\{\sum_{s\in T}c_s s:T\subseteq S\text{ finite},\ c_s\in K\right\}.
$$

Every element of $S$ belongs to $V$ as a one-term combination. The zero vector is the empty sum, or a one-term combination with coefficient zero, since $S$ is nonempty. If $x,y\in V$, choose finite sets supporting their combinations. Extend their coefficients by zero to the union of these sets. Adding the coefficients gives a finite combination representing $x+y$, so $x+y\in V$. For $\lambda\in K$, multiplying every coefficient in a representation of $x$ by $\lambda$ gives $\lambda x\in V$. In particular, $-x\in V$. The remaining vector-space identities are inherited from $X$.

The file also identifies this explicit set with the usual span: every finite combination lies in any subspace containing $S$, while the standard finite-combination description of the span gives the reverse inclusion. The submodule construction therefore has exactly $V$ as its carrier, not a larger set.

**Scope.** Empty sums are permitted. For the source's nonempty $S$, they add no new vector beyond its one-term combinations with coefficient zero.

**Lean declarations:** `exercise01`, `mem_finiteLinearCombinations_iff`.

<a id="r09e02"></a>
### 9.2 — Composition and inverses of linear maps

**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter09/Exercise02.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $X,Y,Z$ be vector spaces over a field $K$. If $A:X\to Y$ and $B:Y\to Z$ are linear, then $B\circ A$ is linear. If $A:X\to X$ is bijective, its inverse is linear and bijective, with inverse $A$. No finite-dimensional or nonzero-space assumption is needed.

**Proof.** For $x,y\in X$ and $c\in K$,

$$
B(A(x+y))=B(Ax)+B(Ay),\qquad B(A(cx))=cB(Ax).
$$

For the inverse claim, first take an ordinary function $g:X\to X$ with $gA=Ag=\operatorname{id}$. The identity $gA=\operatorname{id}$ makes $A$ injective. Applying $A$ to $g(x+y)$ and $g(x)+g(y)$ gives $x+y$ in both cases, so injectivity gives additivity of $g$. Applying $A$ to $g(cx)$ and $cg(x)$ gives $cx$ in both cases, so $g$ preserves scalar multiplication. The two inverse identities also make $g$ injective and surjective, and show that $A$ is its two-sided inverse. For bijective $A$, take the inverse function of its associated bijection and apply these results.

**Lean declarations:** `Rudin.Chapter09.exercise02_composition`, `Rudin.Chapter09.exercise02_inverse_linearity`, `Rudin.Chapter09.exercise02_inverse_invertibility`, `Rudin.Chapter09.exercise02_inverse`.

<a id="r09e03"></a>
### 9.3 — A trivial kernel implies injectivity

**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter09/Exercise03.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $A:X\to Y$ be linear between vector spaces over a field $K$. If $Ax=0$ implies $x=0$, then $A$ is injective. The assertion includes zero-dimensional spaces.

**Proof.** If $Ax=Ay$, linearity gives $A(x-y)=Ax-Ay=0$. The hypothesis gives $x-y=0$, hence $x=y$.

**Lean declarations:** `Rudin.Chapter09.exercise03`.

<a id="r09e04"></a>
### 9.4 — The kernel and range are vector subspaces

**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter09/Exercise04.lean).

**Inventory status:** Verified as stated.

**Statement.** For a linear map $A:X\to Y$ over any field $K$, the sets $\{x:Ax=0\}$ and $A(X)$ are vector subspaces of $X$ and $Y$, respectively, with the inherited operations. No dimension assumption is needed.

**Proof.** The kernel contains zero. If $Ax=Ay=0$, then $A(x+y)=0$, and $A(cx)=cAx=0$ for every scalar $c$. Thus the kernel is closed under addition and scalar multiplication. The range contains $A0=0$; sums and scalar multiples of range elements have the forms $Ax+Ay=A(x+y)$ and $cAx=A(cx)$. These closure properties make both sets subspaces, so their inherited operations satisfy the vector-space axioms. The formal proofs use the library kernel and range subspaces and identify their carriers with these exact sets.

**Lean declarations:** `Rudin.Chapter09.exercise04_kernel`, `Rudin.Chapter09.exercise04_range`.

<a id="r09e05"></a>
### 9.5 — Representing a linear functional by a vector

**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter09/Exercise05.lean).

**Inventory status:** Verified as stated.

**Statement.** For every real linear functional $A:\mathbb R^n\to\mathbb R$, there is a unique $y\in\mathbb R^n$ such that $Ax=x\cdot y$ for all $x$. With the Euclidean norm,

$$
\|A\|=\sup_{\|x\|\leq1}|Ax|=\|y\|.
$$

The result includes $n=0$ and the zero functional. Continuity of $A$ follows from finite dimension; it is not an additional assumption.

**Proof.** Let $e_i$ be the coordinate vectors and set $y_i=Ae_i$. Expanding $x=\sum_i x_i e_i$ gives

$$
Ax=\sum_i x_iAe_i=\sum_i x_i y_i=x\cdot y.
$$

Any other representing vector has the same $i$th coordinate by evaluation at $e_i$, which proves uniqueness. The resulting continuous linear functional is the inner-product functional defined by $y$. Its standard norm theorem gives the norm equality: Cauchy–Schwarz gives $|Ax|\leq\|x\|\|y\|$, and for $y\neq0$ evaluation at $y/\|y\|$ gives equality on the unit ball. If $y=0$, the functional and both norms are zero. This also treats dimension zero. The library closed-unit-ball supremum formula identifies this operator norm with the displayed supremum.

**Lean declarations:** `Rudin.Chapter09.exercise05Vector`, `Rudin.Chapter09.exercise05_representing_vector`, `Rudin.Chapter09.exercise05_uniqueness`, `Rudin.Chapter09.exercise05_existsUnique`, `Rudin.Chapter09.exercise05_norm`, `Rudin.Chapter09.exercise05_source_norm`.

<a id="r09e06"></a>
### 9.6 — Coordinate partials without continuity

**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter09/Exercise06.lean).

**Inventory status:** Verified as stated.

**Statement.** Define $f(0,0)=0$ and

$$
f(x,y)=\frac{xy}{x^2+y^2}\quad\text{for }(x,y)\neq(0,0).
$$

Both coordinate partial derivatives exist everywhere, but $f$ is not continuous at the origin. Away from the origin their values are

$$
D_1f(x,y)=\frac{y(y^2-x^2)}{(x^2+y^2)^2},\qquad
D_2f(x,y)=\frac{x(x^2-y^2)}{(x^2+y^2)^2}.
$$

At the origin both partial derivatives are zero.

**Proof.** For the first partial, fix $y$. If $y=0$, the function of $x$ is identically zero, so its derivative is zero at every $x$. If $y\neq0$, the denominator is positive and the quotient rule gives the first displayed formula. For the second partial, fix $x$. If $x=0$, the function of $y$ is identically zero; otherwise the quotient rule gives the second formula. This proves genuine one-variable derivative existence at every point, including both axes and the origin. Translating the coordinate parameter gives the equivalent derivatives along $p+te_j$ at $t=0$.

On the punctured diagonal, $f(t,t)=1/2$. Were $f$ continuous at the origin, its composition with the continuous curve $t\mapsto(t,t)$ would tend to $f(0,0)=0$. Its punctured limit is instead $1/2$, a contradiction.

**Lean declarations:** `Rudin.Chapter09.exercise06Function_zero`, `Rudin.Chapter09.exercise06_partial_one`, `Rudin.Chapter09.exercise06_partial_two`, `Rudin.Chapter09.exercise06_partials`, `Rudin.Chapter09.exercise06_diagonal`, `Rudin.Chapter09.exercise06_discontinuity`.

<a id="r09e07"></a>
### 9.7 — Bounded partial derivatives imply continuity

**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter09/Exercise07.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open. Suppose every coordinate partial derivative $p_i(x)=D_i f(x)$ exists on $E$, and for each $i$ there is a real bound $C_i$ with $|p_i(x)|\leq C_i$ for all $x\in E$. Then $f$ is continuous on $E$. The partial derivatives need not be continuous. A second formulation assumes one common nonnegative bound $C$.

**Proof.** First use ordinary coordinate space with the supremum norm. Fix $a\in E$ and choose an open cube $Q=\{x:\|x-a\|_\infty<r\}$ contained in $E$. On a coordinate line in this cube, the one-variable function is differentiable throughout its interval. The mean value inequality gives

$$
|f(x)-f(x_1,\ldots,x_{i-1},t,x_{i+1},\ldots,x_n)|\leq C|x_i-t|
$$

whenever both points lie in $Q$. Change the coordinates one at a time from $x$ to $y$. Each intermediate point remains in $Q$, and the triangle inequality gives

$$
|f(x)-f(y)|\leq\sum_{i=1}^n C|x_i-y_i|\leq nC\|x-y\|_\infty.
$$

The formal finite-coordinate estimate is proved by induction on the set of coordinates to be changed. Taking $y=a$ proves continuity; for example, $\delta=\min\{r,\varepsilon/(nC+1)\}$ is sufficient. The continuous coordinate equivalence transfers this result to Euclidean space. For separate coordinate bounds, choose $C=\sum_i|C_i|$, which dominates every partial derivative. Empty domains and $n=0$ are included, with empty sums interpreted as zero.

**Lean declarations:** `Rudin.Chapter09.coordinate_telescope`, `Rudin.Chapter09.continuousOn_of_bounded_coordinate_derivatives`, `Rudin.Chapter09.exercise07`, `Rudin.Chapter09.exercise07_of_coordinate_bounds`.

<a id="r09e08"></a>
### 9.8 — A derivative vanishes at an interior maximum

**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter09/Exercise08.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open and let $f:\mathbb R^n\to\mathbb R$ be differentiable on $E$. If $x\in E$ is a local maximum relative to $E$, then $f$ has the zero Fréchet derivative at $x$; in particular, $f'(x)=0$.

**Proof.** Since $E$ is a neighborhood of $x$, differentiability on $E$ gives ordinary differentiability at $x$, and the relative local maximum is an ordinary local maximum. Apply the standard stationarity theorem for a differentiable real function at a local extremum. This theorem forces its derivative to be zero: restriction to any line through $x$ has a local maximum and hence zero one-variable derivative. The conclusion asserts actual derivative existence with value zero, not merely a value assigned by a total derivative operator.

**Lean declarations:** `Rudin.Chapter09.exercise08`.

<a id="r09e09"></a>
### 9.9 — Zero derivative on a connected open set

**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter09/Exercise09.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open and preconnected, and let $f:\mathbb R^n\to\mathbb R^m$ be differentiable on $E$. If $f'(x)=0$ for every $x\in E$, then there is $c\in\mathbb R^m$ such that $f(x)=c$ for every $x\in E$. Both dimensions are arbitrary, and $E$ may be empty.

**Proof.** Apply the standard zero-derivative constancy theorem on an open preconnected set. Its mean value argument makes $f$ constant on each sufficiently small ball contained in $E$, since such a ball is convex and the derivative vanishes there. Thus $f$ is locally constant on $E$. Preconnectedness makes a locally constant function constant on a nonempty domain. For $E=\varnothing$, choose any vector, for example zero; the assertion is vacuous. Differentiability is essential to the stated hypotheses and is not replaced by the equation for the total derivative operator alone.

**Lean declarations:** `Rudin.Chapter09.exercise09`.

<a id="r09e10"></a>
### 9.10 — Independence of the first coordinate

**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter09/Exercise10.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^{n+1}$ be open and convex. Suppose the first coordinate derivative of $f$ exists and equals zero everywhere on $E$. If $x,y\in E$ have the same coordinates other than the first, then $f(x)=f(y)$. Convexity can be replaced by the weaker requirement that every fiber parallel to the first coordinate axis is preconnected, allowing empty fibers. This weaker requirement is strictly weaker than convexity. Without a domain condition the conclusion can fail.

**Proof.** For a fixed $x$, write $L_x(t)$ for $x$ with its first coordinate replaced by $t$. The set $J_x=L_x^{-1}(E)$ is open. The coordinate derivative assumption says that $t\mapsto f(L_x(t))$ has derivative zero at every $t\in J_x$. If $J_x$ is preconnected, the one-variable zero-derivative theorem makes this function constant on $J_x$. The numbers $x_1$ and $y_1$ belong to this same fiber, which gives $f(x)=f(y)$. For convex $E$, each $J_x$ is convex, because $L_x$ preserves affine combinations, so it is preconnected.

For strict weakness, use $E=\{(x,y):y\neq0\}$. Each horizontal fiber is either all of $\mathbb R$ or empty, so the fiber condition holds. The midpoint of $(0,-1)$ and $(0,1)$ is missing, so $E$ is not convex.

For failure without the fiber condition, use the different open set $E=\{(x,y):x\neq0\}$ and define $f(x,y)=1$ for $x>0$ and $f(x,y)=0$ for $x\leq0$. On $E$ the function is locally constant along each horizontal line, so its first partial derivative exists and is zero. However, $(-1,0)$ and $(1,0)$ have the same second coordinate and different function values. The proved example is this disconnected open set; no horseshoe construction is needed.

**Lean declarations:** `Rudin.Chapter09.firstCoordinateLine`, `Rudin.Chapter09.exercise10_weaker_condition`, `Rudin.Chapter09.exercise10`, `Rudin.Chapter09.exercise10_weaker_not_convex`, `Rudin.Chapter09.exercise10_domain_counterexample`.

<a id="r09e11"></a>
### 9.11 — Gradient product and reciprocal rules

**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter09/Exercise11.lean).

**Inventory status:** Verified as stated.

**Statement.** If real functions $f,g$ on $\mathbb R^n$ are differentiable at $x$, then their product has gradient

$$
\nabla(fg)(x)=f(x)\nabla g(x)+g(x)\nabla f(x).
$$

If $f$ is differentiable at $x$ and $f(x)\neq0$, then its reciprocal has gradient

$$
\nabla(1/f)(x)=-\frac{1}{f(x)^2}\nabla f(x).
$$

Both assertions include existence of the indicated gradient at $x$.

**Proof.** Represent the derivatives of $f$ and $g$ by their gradients using the real inner product. The Fréchet product rule gives $D(fg)(x)=f(x)Dg(x)+g(x)Df(x)$. Linearity of the inner-product representation gives the first gradient. For the reciprocal, compose $f$ with the one-variable function $u\mapsto u^{-1}$, whose derivative at a nonzero $u$ is $-u^{-2}$. The chain rule and the same inner-product representation give the second formula. The nonzero assumption is needed only at the point in question.

**Lean declarations:** `Rudin.Chapter09.exercise11_product`, `Rudin.Chapter09.exercise11_reciprocal`.

<a id="r09e12"></a>
### 9.12 — A torus, its coordinate extrema, and an irrational winding

**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter09/Exercise12.lean).

**Inventory status:** Verified as stated.

**Statement.** Fix $0<a<b$ and define

$$
F(s,t)=((b+a\cos s)\cos t,(b+a\cos s)\sin t,a\sin s),\qquad (s,t)\in\mathbb R^2.
$$

Its range is the compact ring torus

$$
K=\{(x,y,z):(\sqrt{x^2+y^2}-b)^2+z^2=a^2\}.
$$

For the first coordinate $F_1$, the points of $K$ whose entire fibers have zero parameter gradient are exactly

$$
(b+a,0,0),\quad (-(b+a),0,0),\quad (b-a,0,0),\quad (-(b-a),0,0).
$$

These four points are distinct. At every parameter in their respective fibers, the first is a global and local maximum of $F_1$, the second a global and local minimum, and the last two are saddles. There are no other local maxima or minima of $F_1$. The saddle assertion also holds for the first coordinate on $K$ with its relative topology.

For $F_3$, the fibers with zero gradient are exactly the two circles

$$
x^2+y^2=b^2,\qquad z=a\ \text{or}\ z=-a.
$$

The upper circle gives all local maxima, which are global maxima; the lower circle gives all local minima, which are global minima. Finally, if $\lambda$ is irrational, $g(t)=F(t,\lambda t)$ is injective and has range dense in $K$. Its speed satisfies

$$
\|g'(t)\|^2=a^2+\lambda^2(b+a\cos t)^2.
$$

Here a fiber means the full inverse image of a point, not a chosen inverse function.

**Proof.** The radius $r=b+a\cos s$ is strictly positive because $b>a$. The identity $x^2+y^2=r^2$ and $\sin^2s+\cos^2s=1$ show that $F(s,t)\in K$. Conversely, for $(x,y,z)\in K$, set $r=\sqrt{x^2+y^2}$. The surface equation and $b>a$ imply $r>0$. The pairs $((r-b)/a,z/a)$ and $(x/r,y/r)$ lie on the unit circle. Choose angles $s,t$ with these cosine and sine values; then $F(s,t)=(x,y,z)$. Periodicity in both parameters shows that the closed square $[0,2\pi]^2$ has the full range. Its continuous image is compact, proving compactness of $K$.

Differentiation gives

$$
\nabla F_1(s,t)=(-a\sin s\cos t,-(b+a\cos s)\sin t),\qquad
\nabla F_3(s,t)=(a\cos s,0).
$$

The first gradient vanishes exactly when $\sin s=\sin t=0$. Indeed, its second component first forces $\sin t=0$; then $\cos t\neq0$ and the first forces $\sin s=0$. The four choices of the corresponding cosine signs give exactly the four displayed points. Conversely, membership in any of those four fibers forces these sine values to vanish, using the zero second and third coordinates and positivity of the radius. The inequalities $0<a<b$ make all four first coordinates distinct. The third gradient vanishes exactly when $\cos s=0$, or equivalently $\sin s=\pm1$. Thus $z=\pm a$, and the torus equation reduces to $x^2+y^2=b^2$. These arguments apply to every parameter in each fiber.

The bounds $-(b+a)\leq F_1\leq b+a$ and $-a\leq F_3\leq a$ prove the asserted global extrema. At an inner equatorial point, $\cos s=-1$ and $\cos t=\pm1$. For small $h>0$, changing $s$ to $s+h$ changes the radial factor from $b-a$ to $b-a\cos h$, which is larger. Changing $t$ to $t+h$ instead multiplies the first coordinate by $\cos h<1$. According to the sign of $\cos t$, these two perturbations give opposite strict inequalities. They stay in any prescribed parameter neighborhood for sufficiently small $h$. Hence both inner points are saddles and neither is an extremum. Continuity of $F$ transfers the two strict inequalities to points of $K$ in every ambient neighborhood of the corresponding surface point.

Every parameter local extremum has zero gradient. The finite critical-point list therefore reduces the first-coordinate classification to the four cases already considered. At the outer negative point, a small change in $t$ increases the first coordinate, so it is not a maximum; at the outer positive point the same change decreases it, so it is not a minimum. For the third coordinate, at $\cos s=0$ a change from $s$ to $s+h$ multiplies its value by $\cos h$. This excludes a minimum on the upper circle and a maximum on the lower circle, and proves the complete classifications.

To analyze fibers, equality of two torus values first determines the positive radial factors from $x^2+y^2$. It then determines $\cos s,\sin s$ and, after division by that radius, $\cos t,\sin t$. Equality of both sine and cosine is equality modulo $2\pi$. Consequently,

$$
F(s,t)=F(u,v)\quad\Longleftrightarrow\quad
u=s+2\pi k,\quad v=t+2\pi m\quad\text{for some }k,m\in\mathbb Z.
$$

For $g(x)=g(y)$, the fiber equations give $y-x=2\pi k$ and $\lambda(y-x)=2\pi m$. Thus $\lambda k=m$. Irrationality forces $k=0$, and then $x=y$.

For density, fix a target $F(s,t)$. At parameters $s+2\pi n$, with $n\in\mathbb Z$, the first torus angle is unchanged modulo a full turn, while the second angle is $\lambda s+2\pi n\lambda$. The standard irrational-rotation density theorem makes these second angles dense in the circle. The continuous circle parametrization therefore places $F(s,t)$ in the closure of the winding range. The reverse inclusion follows because $K$ is closed and contains the winding range.

Finally, the coordinate product and chain rules give

$$
g'(t)=\bigl(-a\sin t\cos(\lambda t)-\lambda R\sin(\lambda t),\ -a\sin t\sin(\lambda t)+\lambda R\cos(\lambda t),\ a\cos t\bigr),\qquad R=b+a\cos t.
$$

Squaring the Euclidean norm cancels the cross terms. The sine-square and cosine-square identities give the stated speed formula. The derivative and speed formulas themselves hold for all real $a,b,\lambda,t$; irrationality is needed for injectivity and density, not for differentiation.

**Lean declarations:** `Rudin.Chapter09.Exercise12.range_eq_surface`, `Rudin.Chapter09.Exercise12.fundamental_square`, `Rudin.Chapter09.Exercise12.compact_surface`, `Rudin.Chapter09.Exercise12.first_hasGradientAt`, `Rudin.Chapter09.Exercise12.third_hasGradientAt`, `Rudin.Chapter09.Exercise12.first_gradient_zero`, `Rudin.Chapter09.Exercise12.third_gradient_zero`, `Rudin.Chapter09.Exercise12.first_critical`, `Rudin.Chapter09.Exercise12.four_distinct`, `Rudin.Chapter09.Exercise12.first_critical_count`, `Rudin.Chapter09.Exercise12.third_critical`, `Rudin.Chapter09.Exercise12.third_critical_circles`, `Rudin.Chapter09.Exercise12.first_maximum`, `Rudin.Chapter09.Exercise12.first_minimum`, `Rudin.Chapter09.Exercise12.first_saddles`, `Rudin.Chapter09.Exercise12.first_surface_saddles`, `Rudin.Chapter09.Exercise12.first_local_max_iff`, `Rudin.Chapter09.Exercise12.first_local_min_iff`, `Rudin.Chapter09.Exercise12.third_maximum`, `Rudin.Chapter09.Exercise12.third_minimum`, `Rudin.Chapter09.Exercise12.third_local_max_iff`, `Rudin.Chapter09.Exercise12.third_local_min_iff`, `Rudin.Chapter09.Exercise12.fiber_trig`, `Rudin.Chapter09.Exercise12.fibers`, `Rudin.Chapter09.Exercise12.winding_injective`, `Rudin.Chapter09.Exercise12.winding_closure`, `Rudin.Chapter09.Exercise12.winding_hasDerivAt`, `Rudin.Chapter09.Exercise12.speed`.

<a id="r09e13"></a>
### 9.13 — Velocity is tangent to the unit sphere

**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter09/Exercise13.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb R\to\mathbb R^3$ be differentiable and satisfy $\|f(t)\|=1$ for all $t$. Then $f'(t)\cdot f(t)=0$. In geometric terms, for every real $s$ the point $f(t)+sf'(t)$ lies in the affine tangent plane

$$
T_{f(t)}=\{q:(q-f(t))\cdot f(t)=0\}.
$$

Zero velocity is allowed, and $f(t)+s0$ also lies in this plane.

**Proof.** The identity $f(t)\cdot f(t)=1$ has derivative zero. The inner-product product rule gives $f'(t)\cdot f(t)+f(t)\cdot f'(t)=0$. Symmetry of the real inner product makes this $2f'(t)\cdot f(t)=0$. Thus the velocity is perpendicular to the radius. Substituting $q=f(t)+sf'(t)$ into the plane equation gives $s(f'(t)\cdot f(t))=0$. The same substitution for zero velocity gives zero directly. The norm hypothesis also places $f(t)$ on the unit sphere.

**Lean declarations:** `Rudin.Chapter09.exercise13_orthogonality`, `Rudin.Chapter09.sphereTangentPlane`, `Rudin.Chapter09.exercise13_geometry`.

<a id="r09e14"></a>
### 9.14 — Differentiability along curves without a total derivative

**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter09/Exercise14.lean).

**Inventory status:** Verified as stated.

**Statement.** Define $f(0,0)=0$ and $f(x,y)=x^3/(x^2+y^2)$ elsewhere. Its coordinate partials exist everywhere and have uniform absolute bounds $3$ and $2$, respectively. Off the origin they are

$$
A(x,y)=\frac{x^2(x^2+3y^2)}{(x^2+y^2)^2},\qquad
B(x,y)=-\frac{2x^3y}{(x^2+y^2)^2}.
$$

At the origin the partials are $1$ and $0$. The function is continuous on the whole plane. For every direction $u$, the function $t\mapsto f(tu)$ has derivative $f(u)$ at zero; for $\|u\|=1$, this derivative has absolute value at most $1$.

More strongly than the source's specified initial conditions on a curve, every differentiable $\gamma:\mathbb R\to\mathbb R^2$ makes $f\circ\gamma$ differentiable on all of $\mathbb R$. At any parameter $a$,

$$
(f\circ\gamma)'(a)=
\begin{cases}
f(\gamma'(a)),&\gamma(a)=0,\\
A(\gamma(a))\gamma_1'(a)+B(\gamma(a))\gamma_2'(a),&\gamma(a)\neq0.
\end{cases}
$$

If $\gamma$ is $C^1$, so is $f\circ\gamma$. These claims include repeated visits to zero and visits with zero velocity. Nevertheless, $f$ is not Fréchet differentiable at the origin.

**Proof.** For nonzero $p=(x,y)$, the denominator is positive. Algebra gives homogeneity $f(sp)=sf(p)$ for every real $s$, including $s=0$ and $p=0$. Also,

$$
|f(x,y)|=\frac{|x|x^2}{x^2+y^2}\leq|x|.
$$

This bound proves continuity at zero by squeezing, and the quotient formula proves continuity elsewhere.

At a zero of a differentiable curve, put $v=\gamma'(a)$. For $t\neq a$, homogeneity gives

$$
\frac{f(\gamma(t))-f(\gamma(a))}{t-a}=f\left(\frac{\gamma(t)-\gamma(a)}{t-a}\right).
$$

The vector difference quotient tends to $v$, so continuity of $f$ gives the derivative $f(v)$. This proof does not require $v\neq0$. Applying it to $\gamma(t)=tu$ proves all directional derivatives. For unit $u$, the bound $|f(u)|\leq|u_1|\leq\|u\|=1$ gives the required estimate.

Away from zero, the quotient and chain rules give the stated coefficients $A,B$ and the curve derivative formula. Direct estimates give $|A|\leq3$ and $|B|\leq2$: the first follows by comparing $x^2(x^2+3y^2)$ with $3(x^2+y^2)^2$; for the second use $|x||y|\leq x^2+y^2$ and $x^2\leq x^2+y^2$. At zero, the coordinate restrictions are $f(t,0)=t$ and $f(0,t)=0$, which give partials $1,0$ and satisfy the same bounds. Thus the formulas for curves cover every parameter, and the bounded partials also meet the continuity criterion of Exercise 9.7. The direct continuity proof above is the one used in this file.

For the $C^1$ assertion, $A$ and $B$ are continuous away from zero and unchanged by nonzero scalar multiplication. They satisfy the Euler identity

$$
A(p)p_1+B(p)p_2=f(p).
$$

The rational definitions assign $A(0)=B(0)=0$; these assigned coefficient values are not the pair of actual partials at zero. The identity and uniform bounds still hold there. At a parameter with $\gamma(a)\neq0$, the off-zero curve formula and continuity of $\gamma,\gamma'$ prove continuity of $(f\circ\gamma)'$. If $\gamma(a)=\gamma'(a)=0$, use the bound, valid for all $t$,

$$
|(f\circ\gamma)'(t)|\leq3|\gamma_1'(t)|+2|\gamma_2'(t)|.
$$

Its right side tends to zero, which is the derivative at $a$. If $\gamma(a)=0$ but $v=\gamma'(a)\neq0$, extend $w(t)=\gamma(t)/(t-a)$ by $w(a)=v$. Differentiability makes $w$ continuous at $a$ and nonzero nearby. For $t\neq a$ nearby, $\gamma(t)=(t-a)w(t)$, so scale invariance rewrites the derivative as $A(w(t))\gamma_1'(t)+B(w(t))\gamma_2'(t)$. Its limit is $A(v)v_1+B(v)v_2=f(v)$ by the Euler identity. The same formula agrees at $a$. This proves continuity of the derivative in every case.

Finally, if a total derivative $L$ existed at zero, comparison with every line derivative would give $L(u)=f(u)$ for all $u$. For the coordinate vectors, $f(e_1)=1$ and $f(e_2)=0$, whereas $f(e_1+e_2)=1/2$. This contradicts additivity of $L$.

**Lean declarations:** `Rudin.Chapter09.exercise14_value_zero`, `Rudin.Chapter09.exercise14_homogeneous`, `Rudin.Chapter09.exercise14_bound`, `Rudin.Chapter09.exercise14_partials`, `Rudin.Chapter09.exercise14_A_bound`, `Rudin.Chapter09.exercise14_B_bound`, `Rudin.Chapter09.exercise14_continuous`, `Rudin.Chapter09.exercise14_directional`, `Rudin.Chapter09.exercise14_unit_directional`, `Rudin.Chapter09.exercise14_curve_at_zero`, `Rudin.Chapter09.exercise14_curve_off_zero`, `Rudin.Chapter09.exercise14_curve_differentiable`, `Rudin.Chapter09.exercise14_coefficients_scale`, `Rudin.Chapter09.exercise14_euler`, `Rudin.Chapter09.exercise14_coefficients_continuous`, `Rudin.Chapter09.exercise14_curve_deriv_bound`, `Rudin.Chapter09.exercise14_curve_C1`, `Rudin.Chapter09.exercise14_not_differentiable`.

<a id="r09e15"></a>
### 9.15 — Strict minima on lines but not in the plane

**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter09/Exercise15.lean).

**Inventory status:** Verified as stated.

**Statement.** Define $f(0,0)=0$ and, away from zero,

$$
f(x,y)=x^2+y^2-2x^2y-\frac{4x^6y^2}{(x^4+y^2)^2}.
$$

Then $f$ is continuous on the plane. For every unit pair $a^2+b^2=1$, the line restriction $g(t)=f(ta,tb)$ is differentiable at every real parameter and satisfies

$$
g(0)=g'(0)=0,\qquad g''(0)=2.
$$

It has a strict local minimum at zero. In particular, these assertions hold for $a=\cos\theta,b=\sin\theta$ for every real $\theta$, including both endpoints of $[0,2\pi]$. However, $f(x,x^2)=-x^4$ for all real $x$, and zero is not a local minimum in the plane.

**Proof.** Expanding the nonnegative square $(x^4-y^2)^2$ gives

$$
4x^4y^2\leq(x^4+y^2)^2.
$$

For a nonzero point the denominator is positive. Multiplication by $x^2$ and division by its square give

$$
0\leq\frac{4x^6y^2}{(x^4+y^2)^2}\leq x^2.
$$

The rational term is assigned zero at the origin, where the same bound holds. Squeezing makes it continuous there; the quotient rule for continuity applies away from zero. The remaining polynomial terms are continuous, proving continuity of $f$.

For a unit pair, write $g(t)=t^2k(t)$. If $b=0$, then $a^2=1$ and $g(t)=t^2$, so take $k=1$. If $b\neq0$, cancellation for $t\neq0$, with direct checking at $t=0$, gives

$$
k(t)=1-2a^2bt-\frac{4a^6b^2t^2}{(a^4t^2+b^2)^2}.
$$

Its denominator is positive for all $t$, so $k$ is $C^2$ and $k(0)=1$. The product rule gives $g'(t)=2tk(t)+t^2k'(t)$ at every parameter. Differentiating this expression at zero gives $g''(0)=2k(0)=2$, and $g'(0)=g(0)=0$. Since $k$ is positive in a neighborhood of zero, $g(t)=t^2k(t)>0=g(0)$ for all sufficiently small nonzero $t$, proving strict local minimality. The trigonometric unit identity gives every angle case without an endpoint restriction.

Direct substitution on the parabola gives $f(x,x^2)=-x^4$ when $x\neq0$, and both sides vanish when $x=0$. The continuous curve $x\mapsto(x,x^2)$ tends to the origin, but its nonzero points have negative values. A planar local minimum would force these values to be nonnegative for all sufficiently small $x$, which is impossible.

**Lean declarations:** `Rudin.Chapter09.exercise15_zero`, `Rudin.Chapter09.exercise15_inequality`, `Rudin.Chapter09.exercise15_rational_bound`, `Rudin.Chapter09.exercise15_continuous`, `Rudin.Chapter09.exercise15_line_factor`, `Rudin.Chapter09.exercise15_factor_jet`, `Rudin.Chapter09.exercise15_line_derivatives`, `Rudin.Chapter09.exercise15_angles`, `Rudin.Chapter09.exercise15_line_strict_minimum`, `Rudin.Chapter09.exercise15_angle_strict_minimum`, `Rudin.Chapter09.exercise15_curved_values`, `Rudin.Chapter09.exercise15_no_minimum`.

<a id="r09e16"></a>
### 9.16 — An invertible derivative without local injectivity

**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter09/Exercise16.lean).

**Inventory status:** Verified as stated.

**Statement.** Define $f(0)=0$ and $f(x)=x+2x^2\sin(1/x)$ for $x\neq0$. Then $f$ is differentiable on $\mathbb R$, $f'(0)=1$, and

$$
f'(x)=1+4x\sin(1/x)-2\cos(1/x)\quad(x\neq0).
$$

On $(-1,1)$, $|f'(x)|\leq7$. Nevertheless, $f$ is not injective on any neighborhood of zero, despite its invertible derivative at zero.

**Proof.** For $x\neq0$ the difference quotient at zero is $1+2x\sin(1/x)$. Since $|x\sin(1/x)|\leq|x|$, this tends to $1$. At nonzero $x$, the product and chain rules give the displayed derivative, so $f$ is differentiable everywhere. For $0<|x|<1$, the bounds $|\sin u|,|\cos u|\leq1$ give $|f'(x)|\leq1+4|x|+2\leq7$. At zero its derivative is $1$, which satisfies the same bound.

Let

$$
x_n=\frac{1}{2\pi(n+1)},\qquad n=0,1,2,\ldots.
$$

These positive points tend to zero, and their reciprocal angles have sine zero and cosine one. Thus $f'(x_n)=-1$. Suppose $f$ were injective on some interval $(-r,r)$, $r>0$. Since differentiability makes it continuous, the standard theorem for continuous injective functions on an interval says it is strictly increasing or strictly decreasing there. In the increasing case, its derivative must be nonnegative at interior points; some $x_n\in(-r,r)$ contradicts this. In the decreasing case its derivative at zero must be nonpositive, contradicting $f'(0)=1$. Hence it is not injective on any such interval. Every neighborhood of zero contains one, so injectivity fails on every neighborhood. The same derivative sequence shows why derivative continuity at zero, required by the inverse function theorem, is absent here.

**Lean declarations:** `Rudin.Chapter09.exercise16_source`, `Rudin.Chapter09.exercise16_zero`, `Rudin.Chapter09.exercise16_derivative_at_zero`, `Rudin.Chapter09.exercise16_derivative_nonzero`, `Rudin.Chapter09.exercise16_differentiable`, `Rudin.Chapter09.exercise16_bounded_derivative`, `Rudin.Chapter09.exercise16Point_pos`, `Rudin.Chapter09.exercise16Point_limit`, `Rudin.Chapter09.exercise16Point_derivative`, `Rudin.Chapter09.exercise16_not_injOn_interval`, `Rudin.Chapter09.exercise16_not_locally_injective`.

<a id="r09e17"></a>
### 9.17 — The exponential map of the plane

**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter09/Exercise17.lean).

**Inventory status:** Verified as stated.

**Statement.** For $F(x,y)=(e^x\cos y,e^x\sin y)$, the range is $\mathbb R^2\setminus\{0\}$. The map is locally injective everywhere but is not globally injective. At $a=(0,\pi/3)$, put $b=F(a)=(1/2,\sqrt3/2)$. A local inverse taking $b$ to $a$ is

$$
G(w)=(\log|w|,\operatorname{Arg}w),
$$

with principal argument in $(-\pi,\pi)$. Its derivative and the forward derivative are

$$
F'(a)=\begin{pmatrix}1/2&-\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},\qquad
G'(b)=\begin{pmatrix}1/2&\sqrt3/2\\-\sqrt3/2&1/2\end{pmatrix}=F'(a)^{-1}.
$$

Each horizontal line $y=c$ maps onto the open ray $\{r(\cos c,\sin c):r>0\}$; each vertical line $x=c$ maps onto the circle of radius $e^c$.

**Proof.** Identify the Euclidean plane with $\mathbb C$. Then $F(z)=\exp z$, and its real derivative sends $h$ to $e^zh$. In real coordinates its matrix is

$$
\begin{pmatrix}e^x\cos y&-e^x\sin y\\e^x\sin y&e^x\cos y\end{pmatrix},
$$

whose determinant is $e^{2x}>0$. The inverse function theorem gives local injectivity. Global injectivity fails because $F(0)=F(2\pi i)$. The exponential never vanishes, and every nonzero $w$ is $\exp(\log w)$, proving the range claim.

On the strip $-\pi<\operatorname{Im}z<\pi$, the exponential and principal logarithm are continuous inverse maps onto the slit plane. This strip contains $a$, so this is an actual inverse branch near $b$, not just a right inverse. The logarithm derivative is multiplication by $b^{-1}=1/2-i\sqrt3/2$. The displayed matrices therefore represent the actual real derivatives; multiplication in either order gives the identity. Finally, $F(x+ic)=e^xe^{ic}$, and $e^x$ ranges over all positive numbers. For $F(c+iy)$ the norm is $e^c$, and the argument runs around the whole circle.

**Lean declarations:** `Rudin.Chapter09.exercise17_coordinates`, `Rudin.Chapter09.exercise17_euclidean_norm`, `Rudin.Chapter09.exercise17_range`, `Rudin.Chapter09.exercise17_hasFDerivAt`, `Rudin.Chapter09.exercise17_matrix_action`, `Rudin.Chapter09.exercise17_jacobian`, `Rudin.Chapter09.exercise17_jacobian_ne_zero`, `Rudin.Chapter09.exercise17_locally_injective`, `Rudin.Chapter09.exercise17_not_injective`, `Rudin.Chapter09.exercise17_inverse_formula`, `Rudin.Chapter09.exercise17_inverse_branch`, `Rudin.Chapter09.exercise17_inverse_value`, `Rudin.Chapter09.exercise17_b_value`, `Rudin.Chapter09.exercise17_forward_matrix`, `Rudin.Chapter09.exercise17_inverse_hasFDerivAt`, `Rudin.Chapter09.exercise17_inverse_matrix_action`, `Rudin.Chapter09.exercise17_inverse_identity`, `Rudin.Chapter09.exercise17_inverse_eq_matrix_inv`, `Rudin.Chapter09.exercise17_horizontal_image`, `Rudin.Chapter09.exercise17_vertical_image`.

<a id="r09e18"></a>
### 9.18 — The square map and its singular point

**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter09/Exercise18.lean).

**Inventory status:** Verified as stated.

**Statement.** For $F(x,y)=(x^2-y^2,2xy)$, the range is all of $\mathbb R^2$. Its derivative matrix and determinant are

$$
F'(x,y)=\begin{pmatrix}2x&-2y\\2y&2x\end{pmatrix},\qquad \det F'(x,y)=4(x^2+y^2).
$$

It is locally injective exactly away from zero, and it is not globally injective. For $a=(0,\pi/3)$ and $b=(-(\pi/3)^2,0)$, an inverse branch, in complex notation, is

$$
G(w)=i\exp\bigl(\tfrac12\log(-w)\bigr),\qquad w\notin[0,\infty).
$$

This branch takes values in the upper half-plane and satisfies $G(b)=a$. The derivative matrices are

$$
F'(a)=\begin{pmatrix}0&-2\pi/3\\2\pi/3&0\end{pmatrix},\qquad
G'(b)=\begin{pmatrix}0&3/(2\pi)\\-3/(2\pi)&0\end{pmatrix}=F'(a)^{-1}.
$$

Writing image coordinates as $(u,v)$, the image of $y=c\ne0$ is $u=(v/(2c))^2-c^2$, and that of $x=c\ne0$ is $u=c^2-(v/(2c))^2$. The horizontal axis maps onto $v=0$, $u\ge0$; the vertical axis maps onto $v=0$, $u\le0$.

**Proof.** Here $F(z)=z^2$, with real derivative $h\mapsto2zh$, giving the matrix and determinant. For any nonzero $w$, the formula $i\exp(\log(-w)/2)$ has square $w$ by $\exp(\log(-w))=-w$, even outside the continuous branch domain; zero is the square of zero. This proves surjectivity. The inverse function theorem applies at every nonzero $z$. At zero, every neighborhood contains a small nonzero real number and its negative, which have the same square. The pair $1,-1$ also disproves global injectivity.

If $-w$ is in the slit plane, its principal argument lies strictly between $-\pi$ and $\pi$. Thus $\cos(\operatorname{Arg}(-w)/2)>0$, and $G(w)$ has positive imaginary part. Squaring is injective on the upper half-plane: equal squares imply equality or opposite values, and two upper-half-plane points cannot be opposites. It follows that $G(F(z))=z$ there. These open sets give a continuous two-sided branch. The inverse derivative is multiplication by $(2a)^{-1}=-3i/(2\pi)$, which gives the stated matrix; both matrix products are the identity.

On a horizontal line, $u=x^2-c^2$ and $v=2cx$; when $c\ne0$, eliminating $x$ gives the whole stated parabola. The vertical-line calculation is the same with the sign reversed. For $c=0$, squares attain exactly the indicated closed half-axes, including the origin.

**Lean declarations:** `Rudin.Chapter09.exercise18_coordinates`, `Rudin.Chapter09.exercise18_range`, `Rudin.Chapter09.exercise18_hasFDerivAt`, `Rudin.Chapter09.exercise18_matrix_action`, `Rudin.Chapter09.exercise18_jacobian`, `Rudin.Chapter09.exercise18_jacobian_zero_iff`, `Rudin.Chapter09.exercise18_locally_injective_iff`, `Rudin.Chapter09.exercise18_not_injOn_nhds_zero`, `Rudin.Chapter09.exercise18_not_injective`, `Rudin.Chapter09.exercise18_inverse_branch`, `Rudin.Chapter09.exercise18_inverse_value`, `Rudin.Chapter09.exercise18_b_value`, `Rudin.Chapter09.exercise18_forward_matrix`, `Rudin.Chapter09.exercise18_inverse_hasFDerivAt`, `Rudin.Chapter09.exercise18_inverse_matrix_action`, `Rudin.Chapter09.exercise18_inverse_identity`, `Rudin.Chapter09.exercise18_inverse_eq_matrix_inv`, `Rudin.Chapter09.exercise18_horizontal_image`, `Rudin.Chapter09.exercise18_vertical_image`, `Rudin.Chapter09.exercise18_real_axis_image`, `Rudin.Chapter09.exercise18_imaginary_axis_image`.

<a id="r09e19"></a>
### 9.19 — Local graphs of two solution branches

**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter09/Exercise19.lean).

**Inventory status:** Verified as stated.

**Statement.** The solutions of

$$
3x+y-z+u^2=0,\qquad x-y+2z+u=0,\qquad 2x+2y-3z+2u=0
$$

are exactly

$$
u\in\{0,3\},\qquad x=-z/4-u,\qquad y=7z/4.
$$

Near every solution $(x_0,y_0,z_0,u_0)$, the full solution set is a unique smooth graph over any one of $x,y,z$, but not over $u$. Solvability here is local to a branch; it is not global uniqueness across the two lines.

**Proof.** Linear elimination gives $x=-z/4-u$ and $y=7z/4$; substitution leaves $u(u-3)=0$. Conversely, each of these two choices satisfies all three equations. In the open band $|u-u_0|<1$, the other branch is excluded. All solutions in that band therefore have each of the following equivalent descriptions:

$$
(x,y,z,u)=(-z/4-u_0,7z/4,z,u_0),
$$

$$
(x,y,z,u)=(-y/7-u_0,y,4y/7,u_0),
$$

$$
(x,y,z,u)=(x,-7(x+u_0),-4(x+u_0),u_0).
$$

These maps are affine, hence smooth on the open parameter domain $\mathbb R$. Their identities characterize all solutions in the band, so they give local uniqueness as well as existence. To disprove a graph over $u$, vary $x$ slightly in the last formula. Continuity puts a distinct such solution in every prescribed neighborhood of the base solution, while $u$ remains $u_0$. Thus failure follows from actual multiple solutions in the same fiber, not just from a vanishing Jacobian minor.

**Lean declarations:** `Rudin.Chapter09.exercise19_classification`, `Rudin.Chapter09.exercise19_solve_in_z`, `Rudin.Chapter09.exercise19_solve_in_y`, `Rudin.Chapter09.exercise19_solve_in_x`, `Rudin.Chapter09.exercise19_local_graphs`, `Rudin.Chapter09.exercise19_smooth_graphs`, `Rudin.Chapter09.exercise19_failure_in_u`.

<a id="r09e20"></a>
### 9.20 — Geometry of the scalar implicit function theorem

**Lean source:** [Exercise20.lean](../../../Math/Rudin/Chapter09/Exercise20.lean).

**Inventory status:** Verified as stated.

**Statement.** Suppose $f$ is $C^1$ near $(a,b)\in\mathbb R^2$, $f(a,b)=0$, and $D_1f(a,b)\ne0$. The nearby zero set is the unique $C^1$ graph $x=g(y)$, with $g(b)=a$ and

$$
g'(b)=-\frac{D_2f(a,b)}{D_1f(a,b)}.
$$

The coordinate change $H(x,y)=(f(x,y),y)$ maps this local zero graph onto a segment of the vertical line with first coordinate zero. The same construction is proved for $y$ in any real Banach space $Y$, with derivative $g'(b)v=-L(0,v)/L(1,0)$, where $L=f'(a,b)$.

**Proof.** Split the differential as $L(h,v)=L(1,0)h+L(0,v)$. The derivative of $H$ sends $(h,v)$ to $(L(h,v),v)$ and is invertible, with inverse

$$
(s,v)\longmapsto\left(\frac{s-L(0,v)}{L(1,0)},v\right).
$$

Apply the $C^1$ inverse function theorem at $(a,b)$. Its open source and target contain $(a,b)$ and $(0,b)$, respectively. For $y$ in a sufficiently small open neighborhood $W$ of $b$, define $g(y)$ to be the first coordinate of $H^{-1}(0,y)$. The second coordinate is $y$, so $f(g(y),y)=0$. Injectivity of the local coordinate change proves that every zero in its source with $y\in W$ has $x=g(y)$. Its inverse is $C^1$, and evaluating its derivative on $(0,v)$ gives the derivative formula. In the scalar case, restriction of the genuine differential to the two coordinate lines identifies its coefficients with the two partial derivatives. This also explains the graphical proof: invert the coordinate change and pull back the zero line, with uniqueness only inside the chosen local source.

**Lean declarations:** `Rudin.Chapter09.scalarImplicitGraph_exists`, `Rudin.Chapter09.exercise20_graph`, `Rudin.Chapter09.exercise20_partials`, `Rudin.Chapter09.exercise20_proof_graph`.

<a id="r09e21"></a>
### 9.21 — A cubic with a line and an ellipse of zeros

**Lean source:** [Exercise21.lean](../../../Math/Rudin/Chapter09/Exercise21.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f(x,y)=2x^3-3x^2+2y^3+3y^2$. Its stationary points are $(0,0)$, $(0,-1)$, $(1,0)$, and $(1,-1)$. Its only local minimum is the strict minimum $(1,0)$; its only local maximum is the strict maximum $(0,-1)$. The other two stationary points are saddles. Its zero set is exactly

$$
S=\{y=-x\}\ \cup\ \{(x+y)^2+3(x-y-1)^2=3\}.
$$

The ellipse has $-1/2\le x\le3/2$, with branches

$$
y=\frac{2x-3\pm\sqrt{9+12x-12x^2}}4.
$$

The line and ellipse intersect exactly at $(0,0)$ and $(1,-1)$, the only singular zeros. At these nodes the tangent directions are $(h,k)$ with $k=\pm h$.

The full local zero set fails to be a graph $y=y(x)$ exactly at

$$
(0,0),\ (1,-1),\ (3/2,0),\ (-1/2,-1),
$$

and fails to be a graph $x=x(y)$ exactly at

$$
(0,0),\ (1,-1),\ (0,-3/2),\ (1,1/2).
$$

Here a graph means a continuous local graph containing all nearby zeros, not a selected branch.

**Proof.** Differentiation gives $f_x=6x(x-1)$ and $f_y=6y(y+1)$, and the full differential is $f_xh+f_yk$. This gives the four stationary points. The exact increment at $(1,0)$ is

$$
f(x,y)-f(1,0)=(x-1)^2(2x+1)+y^2(2y+3).
$$

Both coefficients are positive near $(1,0)$, and at least one square is positive at every distinct point. The identity $f(1-x,-1-y)=-f(x,y)$ gives the strict maximum at $(0,-1)$. Near zero the two coordinate axes give values of opposite sign. The same reflection gives a saddle at $(1,-1)$. Every local extremum must have zero coordinate derivatives, so this list is exhaustive.

Factorization gives

$$
f(x,y)=(x+y)(2x^2-2xy+2y^2-3x+3y).
$$

Completing squares in the second factor gives the ellipse equation. Solving its quadratic equation in $y$ gives the stated branches and their closed $x$ interval. Substitution of $y=-x$ gives exactly the two intersections. The expansions at them are

$$
f(th,tk)=3t^2(k^2-h^2)+2t^3(h^3+k^3),
$$

$$
f(1+th,-1+tk)=3t^2(h^2-k^2)+2t^3(h^3+k^3).
$$

Thus both intersections have two distinct leading tangent lines.

For graph existence, the implicit function theorem applies wherever the appropriate partial is nonzero. On $S$, solving $f_y=0$ gives exactly the four listed obstructions for $y=y(x)$; solving $f_x=0$ gives the four for $x=x(y)$. Nonzero partials alone do not prove the converse failure. At a node, a continuous ellipse arc and the crossing line give distinct zeros with equal independent coordinate arbitrarily near the node. At $(3/2,0)$, write the two nearby $y$ values as $s(t)\pm t$, where $s(t)=(\sqrt{1-4t^2/3}-1)/2$. Then $6s(t)^2+6s(t)+2t^2=0$, which makes their $y$ contributions equal. A local implicit curve supplies their common $x$ coordinate, giving distinct zeros in the same vertical fiber. Reflection gives the other vertical fold. The symmetry $f(-y,-x)=-f(x,y)$ gives both horizontal folds. These collisions in every neighborhood rule out the full local graph at each listed point.

**Lean declarations:** `Rudin.Chapter09.exercise21_partials`, `Rudin.Chapter09.exercise21_differential`, `Rudin.Chapter09.exercise21_frechet_stationary`, `Rudin.Chapter09.exercise21_extrema`, `Rudin.Chapter09.exercise21_minimum`, `Rudin.Chapter09.exercise21_maximum`, `Rudin.Chapter09.exercise21_stationary_saddles`, `Rudin.Chapter09.exercise21_graph_y`, `Rudin.Chapter09.exercise21_graph_x`, `Rudin.Chapter09.exercise21_zero_set`, `Rudin.Chapter09.exercise21_all_branches`, `Rudin.Chapter09.exercise21_intersections`, `Rudin.Chapter09.exercise21_singular`, `Rudin.Chapter09.exercise21_node_expansions`.

<a id="r09e22"></a>
### 9.22 — A nodal cubic with a loop and two unbounded arms

**Lean source:** [Exercise22.lean](../../../Math/Rudin/Chapter09/Exercise22.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f(x,y)=2x^3+6xy^2-3x^2+3y^2$. Its stationary points are $(0,0)$, a saddle, and $(1,0)$, its unique local minimum, which is strict. There are no local maxima. The zero set $S=\{f=0\}$ is exactly

$$
-1/2<x\le3/2,\qquad y=\pm\sqrt{\frac{x^2(3-2x)}{3+6x}}.
$$

These branches meet only at $(0,0)$ and $(3/2,0)$. The origin is the only singular zero, with tangent lines $y=\pm x$. A parametrization of the entire curve is

$$
P(t)=\left(\frac{3(1-t^2)}{2+6t^2},\frac{3t(1-t^2)}{2+6t^2}\right),\qquad t\in\mathbb R.
$$

The interval $|t|\le1$ gives the loop with $x\ge0$. The remaining parameters give two unbounded arms, both asymptotic to $x=-1/2$: as $t\to+\infty$, $y\to-\infty$, and as $t\to-\infty$, $y\to+\infty$.

On the full zero set, $y=y(x)$ fails locally exactly at $(0,0)$ and $(3/2,0)$. The representation $x=x(y)$ fails exactly at the origin and at

$$
x=\sqrt3/2,\qquad y=\pm\sqrt{\sqrt3/2-3/4}.
$$

**Proof.** The partial derivatives and full differential are

$$
f_x=6(x^2+y^2-x),\qquad f_y=6y(2x+1),\qquad df(h,k)=f_xh+f_yk.
$$

Solving both equations forces $y=0$ and $x=0$ or $1$; the alternative $x=-1/2$ is incompatible with $x^2+y^2-x=0$. The coordinate axes give both signs near zero. At $(1,0)$,

$$
f(x,y)-f(1,0)=(x-1)^2(2x+1)+y^2(6x+3),
$$

which is strictly positive nearby except at the base point. Stationarity is necessary for any local extremum, so there are no others.

The equation $f=0$ rearranges to $(3+6x)y^2=x^2(3-2x)$. Positivity and signs imply $-1/2<x\le3/2$, and division then gives the two branches, including both meeting points. Substitution verifies $f(P(t))=0$. Conversely, a zero with $x\ne0$ is $P(y/x)$; a zero with $x=0$ is the origin, obtained at $t=1$ and $t=-1$. The exact identity

$$
P_1(t)+1/2=\frac2{1+3t^2}
$$

proves the asymptotic $x$ behavior. Since $P_2(t)=tP_1(t)$, it also gives the two limits of $y$. The sign of $1-t^2$ gives the loop parameter interval. At the node,

$$
f(th,tk)=3t^2(k^2-h^2)+2t^3h(h^2+3k^2),
$$

whose quadratic zero directions are precisely $k=\pm h$.

Away from zeros of the relevant partial, the implicit function theorem gives the local graph. On $S$, $f_y=0$ gives only the node and the rightmost point. Reflection in the $x$ axis provides two distinct nearby zeros with the same $x$ at both points. For the other projection, $f_x=0$ on $S$ gives the node or $x>0$, $4x^2=3$, $y^2=x-x^2$, yielding the stated two folds. To prove actual failure, not just failure of an implicit-function hypothesis, divide the cubic in $x$ by a known root. The other roots are

$$
z=\frac{3-2x\pm\sqrt{9+12x-12x^2-48y^2}}4.
$$

Near the node, a parametrized zero and the minus choice give distinct roots in the same horizontal fiber that converge to the node. At either fold, an implicit zero curve and the plus choice do the same. The discriminant is positive nearby; equality of the two roots would force $f_x=0$, which the punctured curves exclude. Thus all listed points, and only those points, fail the full local graph condition.

**Lean declarations:** `Rudin.Chapter09.exercise22_partials`, `Rudin.Chapter09.exercise22_differential`, `Rudin.Chapter09.exercise22_frechet_stationary`, `Rudin.Chapter09.exercise22_extrema`, `Rudin.Chapter09.exercise22_minimum`, `Rudin.Chapter09.exercise22_stationary_saddles`, `Rudin.Chapter09.exercise22_graph_y`, `Rudin.Chapter09.exercise22_graph_x_explicit`, `Rudin.Chapter09.exercise22_zero_set`, `Rudin.Chapter09.exercise22_branches`, `Rudin.Chapter09.exercise22_param_surjective`, `Rudin.Chapter09.exercise22_singular`, `Rudin.Chapter09.exercise22_branch_meetings`, `Rudin.Chapter09.exercise22_node_expansion`, `Rudin.Chapter09.exercise22_tangent_cone`, `Rudin.Chapter09.exercise22_loop_parameters`, `Rudin.Chapter09.exercise22_asymptotes`.

<a id="r09e23"></a>
### 9.23 — Derivatives of an implicitly defined function

**Lean source:** [Exercise23.lean](../../../Math/Rudin/Chapter09/Exercise23.lean).

**Inventory status:** Verified as stated.

**Statement.** For $f(x,y_1,y_2)=x^2y_1+e^x+y_2$, there is an open neighborhood $W$ of $(1,-1)$ and a $C^1$ function $g:W\to\mathbb R$ such that

$$
g(1,-1)=0,\qquad g(y_1,y_2)^2y_1+e^{g(y_1,y_2)}+y_2=0.
$$

This graph is unique inside a suitable open neighborhood of $(0,1,-1)$. At the base point, $D_1g=0$ and $D_2g=-1$.

**Proof.** The function is $C^1$, $f(0,1,-1)=0$, and its differential there is $(h,k_1,k_2)\mapsto h+k_2$. In particular the $x$ partial exists and equals $1\ne0$. Apply the scalar implicit-graph construction, grouping $(y_1,y_2)$ as a Banach-space variable. Its derivative formula gives $g'(1,-1)(k_1,k_2)=-k_2$. Restriction to each coordinate line gives the asserted partial derivatives as actual one-variable derivatives. The inverse-function construction supplies the open domain, $C^1$ regularity, equation, base value, and local uniqueness for this same function $g$.

**Lean declarations:** `Rudin.Chapter09.exercise23_zero_value`, `Rudin.Chapter09.exercise23_differential`, `Rudin.Chapter09.exercise23_nonzero_partial`, `Rudin.Chapter09.exercise23_implicit_function`, `Rudin.Chapter09.exercise23_graph_differential`, `Rudin.Chapter09.exercise23_first_partial`, `Rudin.Chapter09.exercise23_second_partial`.

<a id="r09e24"></a>
### 9.24 — A rank-one map onto an ellipse

**Lean source:** [Exercise24.lean](../../../Math/Rudin/Chapter09/Exercise24.lean).

**Inventory status:** Verified as stated.

**Statement.** On the punctured Euclidean plane let

$$
F(x,y)=\left(\frac{x^2-y^2}{x^2+y^2},\frac{xy}{x^2+y^2}\right).
$$

Its derivative has rank $1$ at every point of its domain. Its exact range is the ellipse $u^2+4v^2=1$; the second numerator is $xy$, not $2xy$.

**Proof.** Put $d=x^2+y^2>0$. The quotient rule factors the actual derivative as

$$
F'(x,y)(h,k)=(yh-xk)\left(\frac{4xy}{d^2},\frac{y^2-x^2}{d^2}\right).
$$

The linear functional is nonzero because $(x,y)\ne0$. The vector is nonzero as well: if $xy=0$ and $y^2=x^2$, then both coordinates vanish. The range of this derivative is therefore exactly the one-dimensional span of that vector, proving the rank statement even on either coordinate axis.

Direct expansion gives $F_1^2+4F_2^2=1$. Conversely, take $(u,v)$ on the ellipse. If $u=-1$, the equation gives $v=0$, and $F(0,1)=(-1,0)$. Otherwise use the nonzero preimage $(1+u,2v)$. The ellipse equation gives $(1+u)^2+(2v)^2=2(1+u)$, and substitution into $F$ gives $(u,v)$. This includes all boundary points of the ellipse and proves equality of ranges.

**Lean declarations:** `Rudin.Chapter09.exercise24_hasFDerivAt`, `Rudin.Chapter09.exercise24_rank`, `Rudin.Chapter09.exercise24_on_ellipse`, `Rudin.Chapter09.exercise24_range`.

<a id="r09e25"></a>
### 9.25 — A projection from a right inverse on the range

**Lean source:** [Exercise25.lean](../../../Math/Rudin/Chapter09/Exercise25.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $A:E\to F$ be real linear. There is a linear map $S:\operatorname{range}A\to E$ with $AS=\operatorname{id}$ on the range. For any such $S$, the map $P=SA:E\to E$ satisfies

$$
P^2=P,\qquad \ker P=\ker A,\qquad \operatorname{range}P=\operatorname{range}S.
$$

If $E$ is finite-dimensional, then $\dim\ker A+\dim\operatorname{range}A=\dim E$. In particular, for $A:\mathbb R^n\to\mathbb R^m$ of rank $r$, $\dim\ker A+r=n$, including rank zero and dimension zero.

**Proof.** The surjective linear map $A:E\to\operatorname{range}A$ has a linear right inverse, obtained by choosing preimages of a basis. Its right-inverse identity gives $P^2=S(AS)A=SA$. If $Px=0$, applying $A$ gives $Ax=0$; the converse follows from linearity of $S$. Every $Px$ lies in the range of $S$, and every $Sz$ is $SAx$ for a preimage $x$ of $z$, proving the range identity.

An idempotent splits $E$ into the complementary subspaces $\ker P$ and $\operatorname{range}P$: $x=(x-Px)+Px$, and their intersection is zero. Also $S$ is injective because $AS$ is the identity. Thus $\dim\operatorname{range}S=\dim\operatorname{range}A$, and taking dimensions in this splitting proves the formula. No division by $r$ occurs. For $A=0$, $S$ is the unique map from the zero range and $P=0$, so the same argument applies.

**Lean declarations:** `Rudin.Chapter09.exercise25_right_inverse`, `Rudin.Chapter09.exercise25_projection`, `Rudin.Chapter09.exercise25_kernel`, `Rudin.Chapter09.exercise25_range`, `Rudin.Chapter09.exercise25_dimension`, `Rudin.Chapter09.exercise25_b`.

<a id="r09e26"></a>
### 9.26 — A continuous mixed partial without a first partial

**Lean source:** [Exercise26.lean](../../../Math/Rudin/Chapter09/Exercise26.lean).

**Inventory status:** Verified as stated.

**Statement.** For any nowhere differentiable $g:\mathbb R\to\mathbb R$, let $f(x,y)=g(x)$. Then $D_2f=0$ everywhere, and $D_{12}f=D_1(D_2f)=0$ is continuous everywhere, although $D_1f$ exists nowhere. The source also supplies a concrete such $g$: it is $1$ on rational numbers and $0$ on irrational numbers. Continuity of $f$ is not asserted or required.

**Proof.** For fixed $x$, the function of $y$ is constant, so its derivative genuinely exists and equals zero. For fixed $y$, this proved inner derivative is the zero function of $x$, so its derivative also exists and equals zero. Hence the mixed partial is a continuous constant function. In contrast, the $x$ slice is exactly $g$, and is nowhere differentiable by hypothesis.

For the concrete example, every interval contains both a rational and an irrational number. If $g$ were continuous at any $x$, a sufficiently small neighborhood would force $|g(t)-g(x)|<1/2$. Choosing $t$ of the opposite rationality gives difference $1$, a contradiction. Thus $g$ is nowhere continuous and therefore nowhere differentiable. This verifies that the construction has an actual example, rather than only a conditional hypothesis.

**Lean declarations:** `Rudin.Chapter09.exercise26_second_partial`, `Rudin.Chapter09.exercise26_mixed_partial`, `Rudin.Chapter09.exercise26_mixed_continuous`, `Rudin.Chapter09.exercise26_first_nowhere`, `Rudin.Chapter09.exercise26_nowhere_not_continuous`, `Rudin.Chapter09.exercise26_nowhere_not_differentiable`, `Rudin.Chapter09.exercise26_example`.

<a id="r09e27"></a>
### 9.27 — Continuous first partials and unequal mixed partials

**Lean source:** [Exercise27.lean](../../../Math/Rudin/Chapter09/Exercise27.lean).

**Inventory status:** Verified as stated.

**Statement.** Set $f(0,0)=0$ and, elsewhere,

$$
f(x,y)=\frac{xy(x^2-y^2)}{x^2+y^2}.
$$

The function is $C^1$ on the entire plane. Both mixed partials exist everywhere and are continuous off the origin, but both are discontinuous there. With the rightmost derivative taken first,

$$
D_{12}f(0,0)=1,\qquad D_{21}f(0,0)=-1.
$$

**Proof.** The first partials have $P(0,0)=Q(0,0)=0$ and, off the origin, are

$$
P(x,y)=\frac{y(x^4+4x^2y^2-y^4)}{(x^2+y^2)^2},\qquad Q(x,y)=-P(y,x).
$$

For the first partial, the slice $y=0$ is constant zero; for $y\ne0$, the quotient rule gives $P$. Antisymmetry $f(x,y)=-f(y,x)$ gives the second partial. The estimates

$$
|f(x,y)|\le |x||y|,\qquad |P(x,y)|\le3|y|,\qquad |Q(x,y)|\le3|x|
$$

prove continuity of all three at zero. Away from zero they are rational functions with nonzero denominator. Continuous first partials then give the actual continuous total derivative, hence $C^1$ regularity.

For $(x,y)\ne(0,0)$ put

$$
K(x,y)=\frac{x^6+9x^4y^2-9x^2y^4-y^6}{(x^2+y^2)^3}.
$$

For $(x,y)\ne(0,0)$, direct differentiation gives $D_{21}f=K(x,y)$ and $D_{12}f=-K(y,x)$. On the vertical axis, the identity $P(0,y)=-y$ proves the derivative of $P$ directly, including $D_{21}f(0,0)=-1$; the swapped identity gives $D_{12}f(0,0)=1$. Thus these are derivatives of the actual first partials, not values assigned to nonexistent derivatives.

The formulas with $K$ prove continuity away from zero. For nonzero $x$, $D_{21}f(x,0)=1$, contrary to its value $-1$ at zero. For nonzero $y$, $D_{12}f(0,y)=-1$, contrary to its value $1$ at zero. Restricting any alleged continuity to these axes gives contradictions.

**Lean declarations:** `Rudin.Chapter09.exercise27_zero`, `Rudin.Chapter09.exercise27_continuous`, `Rudin.Chapter09.exercise27_first_partials`, `Rudin.Chapter09.exercise27_actual_first_partials`, `Rudin.Chapter09.exercise27_C1`, `Rudin.Chapter09.exercise27_mixed_existence`, `Rudin.Chapter09.exercise27_mixed_continuous_off_zero`, `Rudin.Chapter09.exercise27_mixed_discontinuous`, `Rudin.Chapter09.exercise27_D12_zero`, `Rudin.Chapter09.exercise27_D21_zero`, `Rudin.Chapter09.exercise27_mixed_values`, `Rudin.Chapter09.exercise27_D12_formula`, `Rudin.Chapter09.exercise27_D21_formula`.

<a id="r09e28"></a>
### 9.28 — Failure to interchange differentiation and integration

**Lean source:** [Exercise28.lean](../../../Math/Rudin/Chapter09/Exercise28.lean).

**Inventory status:** Verified as stated.

**Statement.** For $t\ge0$, define

$$
\phi(x,t)=\begin{cases}
x,&0\le x\le\sqrt t,\\
-x+2\sqrt t,&\sqrt t\le x\le2\sqrt t,\\
0,&\text{otherwise},
\end{cases}
$$

and for $t<0$ set $\phi(x,t)=-\phi(x,|t|)$. The closed pieces agree at their shared endpoints. This function is jointly continuous on $\mathbb R^2$, and $D_2\phi(x,0)=0$ for every real $x$. Nevertheless, if $I(t)=\int_{-1}^1\phi(x,t)\,dx$, then $I(t)=t$ for $|t|<1/4$, so

$$
I'(0)=1\ne0=\int_{-1}^1D_2\phi(x,0)\,dx.
$$

The integrals are verified both as ordinary interval integrals and as the source's closed-cell Darboux and tagged-refinement integrals.

**Proof.** Write $T(x,r)=\max(0,\min(x,2r-x))$. For $r\ge0$, it equals $x$ on $[0,r]$, $2r-x$ on $[r,2r]$, and zero outside, with matching endpoint values. Also $0\le T(x,r)\le r$. Away from $t=0$, continuity follows from the min/max formula and the locally constant choice of sign. At every point of the whole $t=0$ axis, the bound $|\phi(x,t)|\le\sqrt{|t|}$ proves continuity, since $\phi(x,0)=0$.

For fixed $x\le0$, $\phi(x,t)$ is always zero. For fixed $x>0$, $2\sqrt{|t|}<x$ for all sufficiently small $t$, so the function is again identically zero near $t=0$. Its parameter derivative is therefore an actual derivative equal to zero for every $x$.

Every slice in $x$ is continuous and hence integrable on each finite interval. If $r\ge0$ and $2r\le1$, split $[-1,1]$ at $0,r,2r$. The two nonzero integrals are each $r^2/2$, so the total is $r^2$, including the degenerate case $r=0$. Take $r=\sqrt{|t|}$ and use the sign in the definition: the result is $t$ when $|t|<1/4$. Thus $I$ agrees with the identity near zero and $I'(0)=1$.

For completeness, the source integral is the supremum of lower sums over weakly increasing partitions of $[-1,1]$, using infima on closed cells. The continuous-integrand bridge for the integrator $\alpha(x)=x$ identifies this value with the interval integral, and also proves equality with upper sums and the tagged-refinement criterion. The parameter partial is identically zero, so its Darboux and interval integrals both equal zero. Hence neither side of the failed interchange relies on an undefined derivative or an unproved integrability assumption.

**Lean declarations:** `Rudin.Chapter09.exercise28_piecewise`, `Rudin.Chapter09.exercise28_source_nonnegative`, `Rudin.Chapter09.exercise28_source_negative`, `Rudin.Chapter09.exercise28_continuous`, `Rudin.Chapter09.exercise28_parameter_partial`, `Rudin.Chapter09.exercise28_slice_integrable`, `Rudin.Chapter09.exercise28_darboux_bridge`, `Rudin.Chapter09.exercise28_source_integral`, `Rudin.Chapter09.exercise28_integral_value`, `Rudin.Chapter09.exercise28_failed_interchange`, `Rudin.Chapter09.exercise28_failed_interchange_interval`, `Rudin.Chapter09.exercise28_tent_integral`, `Rudin.Chapter09.exercise28_integral_derivative`, `Rudin.Chapter09.exercise28_partial_integral`.

<a id="r09e29"></a>
### 9.29 — Permutation of coordinate derivatives

**Lean source:** [Exercise29.lean](../../../Math/Rudin/Chapter09/Exercise29.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open and $f\in C^m(E)$. Every ordered coordinate derivative of length $k\le m$ is unchanged by a permutation of its indices, including repeated indices. In particular, for $f\in C^k(E)$,

$$
D_{i_{\sigma(1)}}\cdots D_{i_{\sigma(k)}}f(a)=D_{i_1}\cdots D_{i_k}f(a),\qquad a\in E.
$$

The empty list gives $f$ itself. All intermediate derivatives used here genuinely exist: a derivative of length $j$ is $C^r$ whenever $j+r\le m$.

**Proof.** Define a coordinate derivative by applying the Fréchet derivative to the corresponding Euclidean coordinate vector, and iterate from the right. Induction on the list length proves the remaining regularity statement by differentiating a $C^{r+1}$ function and evaluating on a fixed vector. If the length is less than $m$, this gives an existing Fréchet derivative. Composition with $t\mapsto a+te_i$ proves that the next coordinate derivative is also the ordinary one-variable partial at $t=0$.

For a $C^2$ function, symmetry of the continuous second Fréchet derivative gives $D_iD_jg=D_jD_ig$. Now use that adjacent swaps generate permutations. A swap of two leading indices is valid because the remaining inner derivative is $C^2$. If a permutation is already valid for an inner list, the resulting functions agree throughout $E$; openness makes them equal near every $a\in E$, so their next derivatives agree there too. Transitivity completes the induction over permutations. This proves equality of actual coordinate derivatives without assuming symmetry of a higher differential as a separate hypothesis.

**Lean declarations:** `Rudin.Chapter09.mixedPartial_contDiffOn`, `Rudin.Chapter09.mixedPartial_hasFDerivAt`, `Rudin.Chapter09.mixedPartial_hasDerivAt`, `Rudin.Chapter09.coordinatePartial_comm`, `Rudin.Chapter09.exercise29_permutation_invariance`, `Rudin.Chapter09.exercise29_ordered_permutation`.

<a id="r09e30"></a>
### 9.30 — Ordered and multi-index Taylor expansions

**Lean source:** [Exercise30.lean](../../../Math/Rudin/Chapter09/Exercise30.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open, $m\ge1$, $f\in C^m(E)$, and $a\in E$. For $h(t)=f(a+tx)$, at every parameter with $a+tx\in E$ and for $0\le k\le m$,

$$
h^{(k)}(t)=\sum_{i_1,\ldots,i_k=1}^n(D_{i_1}\cdots D_{i_k}f)(a+tx)x_{i_1}\cdots x_{i_k}.
$$

The $k=0$ expression is $f(a+tx)$. If the entire segment $a+tx$, $0\le t\le1$, lies in $E$, then

$$
f(a+x)=\sum_{k=0}^{m-1}\frac1{k!}\sum_{i_1,\ldots,i_k=1}^n(D_{i_1}\cdots D_{i_k}f)(a)x_{i_1}\cdots x_{i_k}+r(x).
$$

The actual remainder has both forms

$$
r(x)=\frac1{(m-1)!}\int_0^1(1-t)^{m-1}D^mf(a+tx)[x,\ldots,x]\,dt
=\frac1{m!}D^mf(a+\theta x)[x,\ldots,x]
$$

for some $0<\theta<1$. Locally $r(x)=O(|x|^m)$, and hence

$$
\frac{r(x)}{|x|^{m-1}}\longrightarrow0\qquad(x\to0,\ x\ne0).
$$

The same polynomial, with the same remainder, is

$$
\sum_{s_1+\cdots+s_n\le m-1}\frac{(D_1^{s_1}\cdots D_n^{s_n}f)(a)}{s_1!\cdots s_n!}x_1^{s_1}\cdots x_n^{s_n},
$$

where all $s_i$ are nonnegative integers. These results include $m=1$ and dimension zero, with the usual empty-sum and empty-product conventions.

**Proof.** First identify each ordered coordinate derivative with $D^kf$ evaluated on its coordinate vectors. Induction uses the existing derivative of $D^{k-1}f$ and local equality on the open domain. Expand each copy of $x=\sum_i x_ie_i$ by multilinearity. The resulting diagonal evaluation is exactly the ordered coordinate sum.

The chain rule gives a genuine derivative jet along the line: the derivative of $D^kf(a+tx)[x,\ldots,x]$ is $D^{k+1}f(a+tx)[x,\ldots,x]$ for $k<m$. The inverse image of $E$ under the line map is open, so local equality and induction identify this jet with the iterated scalar derivatives of $h$. This proves the formula wherever the line is in $E$, not just inside the specified segment.

Apply one-variable Taylor theory on $[0,1]$ to obtain the integral and Lagrange remainders. The integral remainder integrand is continuous on the whole segment, hence integrable. Continuity of $D^mf$ near $a$ gives a ball on which its operator norm is bounded by a constant $C$. For sufficiently small $x$, the full segment is in this ball. Multilinearity gives $|D^mf(a+tx)[x,\ldots,x]|\le C|x|^m$; also $0\le(1-t)^{m-1}\le1$. The integral formula therefore bounds $|r(x)|$ by a fixed constant times $|x|^m$. Since $|x|^m=o(|x|^{m-1})$, the required little-o estimate and punctured limit follow. When $m=1$, this is $r(x)\to0$; in dimension zero the punctured limit has no nonzero points.

Finally group the ordered $k$-tuples by their coordinate multiplicities $s=(s_1,\ldots,s_n)$. The exact number with these multiplicities is $k!/(s_1!\cdots s_n!)$. The source proves this count by comparing the coefficient of the corresponding monomial in the ordered and multinomial expansions of $(X_1+\cdots+X_n)^k$. Exercise 29 makes the derivative identical for all tuples in a group, and their products all equal $x_1^{s_1}\cdots x_n^{s_n}$. Cancel the factor $k!$ against the Taylor coefficient. Taking the union of the groups for $0\le k<m$ gives exactly total degree at most $m-1$, including the constant term, and proves equality of the two polynomials.

**Lean declarations:** `Rudin.Chapter09.mixedPartial_eq_iteratedFDeriv`, `Rudin.Chapter09.orderedCoordinateSum_eq`, `Rudin.Chapter09.exercise30_sourceJet`, `Rudin.Chapter09.line_iteratedDeriv`, `Rudin.Chapter09.exercise30_a`, `Rudin.Chapter09.exercise30_b_expansion`, `Rudin.Chapter09.exercise30_b_lagrange`, `Rudin.Chapter09.orderedCoordinateSum_zero`, `Rudin.Chapter09.taylorRemainder_intervalIntegrable`, `Rudin.Chapter09.taylorRemainder_isBigO`, `Rudin.Chapter09.exercise30_b_remainder_isLittleO`, `Rudin.Chapter09.exercise30_b_remainder`, `Rudin.Chapter09.Exercise30Combinatorics.card_counts_fiber`, `Rudin.Chapter09.Exercise30Combinatorics.sum_list_perm_invariant`, `Rudin.Chapter09.mem_taylorMultiIndices_iff`, `Rudin.Chapter09.exercise30_c`, `Rudin.Chapter09.exercise30_multiIndex_expansion`.

<a id="r09e31"></a>
### 9.31 — Corrected second-derivative tests and a singular obstruction

**Lean source:** [Exercise31.lean](../../../Math/Rudin/Chapter09/Exercise31.lean).

**Inventory status:** Verified refutation and correction.

**Statement.** The printed claim is false: $C^3$ regularity near a stationary point and at least one nonzero second partial do not ensure that the quadratic Taylor polynomial determines the type of local extremum. The smooth planar functions

$$
f_+(x,y)=x^2+y^4,\qquad f_-(x,y)=x^2-y^4
$$

have the same value, zero gradient, nonzero singular Hessian $\operatorname{diag}(2,0)$, and quadratic Taylor polynomial $x^2$ at zero. The first has a strict global minimum there; the second has neither a local minimum nor a local maximum. The obstruction extends to every dimension at least two, and negation gives the corresponding negative-semidefinite obstruction.

The valid tests are as follows. Suppose $f$ is $C^3$ near $a$ in a finite-dimensional real normed space and $f'(a)=0$, and let $B=f''(a)$ be its actual Hessian. If $B(v,v)>0$ for every $v\ne0$, then $a$ is a strict local minimum. If $B(v,v)<0$ for every $v\ne0$, it is a strict local maximum. If $B$ has both a positive and a negative quadratic direction, it is neither a local minimum nor a local maximum. A nonzero positive-semidefinite Hessian excludes a local maximum but does not decide whether a local minimum exists; reverse the signs for a negative-semidefinite Hessian. In dimension one a nonzero Hessian is decisive by its sign. In dimension zero the nonzero-Hessian hypothesis is impossible.

**Proof.** The source first derives the genuine quadratic expansion

$$
f(a+h)-f(a)=\tfrac12B(h,h)+o(|h|^2).
$$

Local $C^3$ regularity supplies first derivatives in a neighborhood and differentiability of the derivative at $a$. Symmetry of this second derivative makes the derivative of $B(x-a,x-a)/2$ equal to $B(x-a,\cdot)$. Subtract this quadratic function and $f(a)$ from $f$. The resulting derivative is $o(|x-a|)$. The mean-value estimate on a small convex ball then gives an error $o(|x-a|^2)$, proving the expansion rather than assuming it.

For positive definite $B$, continuity and compactness of the unit sphere give $c>0$ with $B(h,h)\ge c|h|^2$. Choose the error smaller than $(c/4)|h|^2$. The increment is then positive for every sufficiently small nonzero $h$, giving a strict minimum on a full punctured neighborhood. Negation proves the negative definite test. A positive direction $v$ gives $f(a+tv)>f(a)$ for sufficiently small nonzero $t$, so it excludes a local maximum; a negative direction excludes a local minimum. Both directions give the indefinite conclusion. These directional exclusions do not require finite dimension.

For the semidefinite conclusion, a symmetric nonzero positive-semidefinite form has a positive direction. Otherwise all diagonal values vanish, and expansion of $B(v+w,v+w)$ with symmetry forces every $B(v,w)$ to vanish, a contradiction. Apply the directional exclusion, and negate for the negative case. In one dimension $B(x,y)=xyB(1,1)$, so $B\ne0$ implies $B(1,1)\ne0$ and one of the definite tests applies. On a zero-dimensional space every bilinear form is zero.

To show exactly why the singular cases remain inconclusive, in dimension $d\ge2$ define

$$
F_c(p)=\sum_{j\ne2}p_j^2+c\,p_2^4.
$$

For every $c$, these polynomial functions have value and first derivative zero at the origin and the same Hessian

$$
B(v,w)=2\sum_{j\ne2}v_jw_j.
$$

This Hessian is nonnegative, is nonzero on the first coordinate vector, and has the nonzero second coordinate vector in its kernel. The actual quadratic Taylor polynomial is $\sum_{j\ne2}h_j^2$, independent of $c$. For $c=1$, every nonzero point has positive value, giving a strict global and local minimum. For $c=-1$, the first axis has values $t^2>0$ and the second has values $-t^4<0$ arbitrarily close to zero, giving neither extremum. Their negatives have the same negative-semidefinite quadratic polynomial; one has a strict local maximum and the other has neither extremum. For $d=2$ these are exactly the displayed planar examples. Thus the source's original classification is refuted, while all stated corrected tests retain their full hypotheses and singular cases.

**Lean declarations:** `Rudin.Chapter09.exercise31_counterexample`, `Rudin.Chapter09.exercise31_planar_formula`, `Rudin.Chapter09.exercise31_counter_hessian_axis`, `Rudin.Chapter09.exercise31_zero_dimension`, `Rudin.Chapter09.exercise31_one_dimension`, `Rudin.Chapter09.exercise31_counter_hessian_nonnegative`, `Rudin.Chapter09.exercise31_counter_hessian_nonzero`, `Rudin.Chapter09.exercise31_counter_hessian_kernel`, `Rudin.Chapter09.exercise31_counter_same_jet`, `Rudin.Chapter09.exercise31_counter_taylor`, `Rudin.Chapter09.exercise31_counter_negative_jet`, `Rudin.Chapter09.exercise31_counter_negative_taylor`, `Rudin.Chapter09.exercise31_counter_negative_behavior`, `Rudin.Chapter09.exercise31_quadratic_expansion`, `Rudin.Chapter09.exercise31_positive_test`, `Rudin.Chapter09.exercise31_negative_test`, `Rudin.Chapter09.exercise31_indefinite_test`, `Rudin.Chapter09.exercise31_semidefinite_exclusions`, `Rudin.Chapter09.exercise31_counter_minimum`, `Rudin.Chapter09.exercise31_counter_neither`.
