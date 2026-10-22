# Rudin progress

Generated from `exercises.json`. Do not edit counts by hand.

| Chapter | Verified resolutions | As stated | Refuted/corrected | Verified obligations |
| --- | --- | --- | --- | --- |
| 1 | 2/20 | 1 | 1 | 6/55 |
| 2 | 1/30 | 1 | 0 | 1/71 |
| 3 | 1/25 | 1 | 0 | 8/88 |
| 4 | 0/26 | 0 | 0 | 0/73 |
| 5 | 0/29 | 0 | 0 | 0/81 |
| 6 | 1/19 | 1 | 0 | 2/52 |
| 7 | 0/26 | 0 | 0 | 0/79 |
| 8 | 0/31 | 0 | 0 | 0/79 |
| 9 | 1/31 | 1 | 0 | 1/110 |
| 10 | 0/32 | 0 | 0 | 0/114 |
| 11 | 2/18 | 1 | 1 | 5/37 |

Total: **8/287 verified resolutions**; **23/839 obligations** verified.

These comprise 6 exercises proved as stated and 2 false source claims resolved by counterexamples and explicit corrections. A refuted claim is not counted as a proved original statement.

## Source issues and blockers

- `R02E28`: The isolated-point corollary needs a nonempty set if countable includes finite sets. Under Rudin's strict countably-infinite meaning, it excludes the empty set already; preserve this distinction when translating to Lean Countable.
- `R02E29`: Unbounded open sets require rays or R itself among the components. If the earlier term segment requires two real endpoints, the literal assertion is false. The endpoint convention needs an explicit decision rather than a silent correction.
- `R03E06`: Part (d) asks about complex z without excluding z^n=-1 for some positive n. Such parameters make at least one term undefined; distinguish them from divergent series and do not use totalized field division to erase this case.
- `R03E18`: The reference to Exercise 16 leaves the intended starting bound implicit: x_1>sqrt(alpha) is not the same as x_1>alpha^(1/p). Inventory retains the inherited condition; intended monotonicity and any alternative initial condition need an explicit decision.
- `R04E09`: The displayed all-subsets formulation includes empty E, but Definition 3.9 defines diameter only for nonempty sets. Explicitly restrict to nonempty E or document the harmless extension diam(empty)=0; do not silently assume the source already defines it.
- `R05E13`: For arbitrary real a, the printed x^a is not a real-valued expression on negative x under the usual real-power convention. The likely |x|^a correction must be confirmed before formalization; none of the seven claims has been proved here.
- `R05E25`: Part (b) is false after finite termination: an affine f satisfying the hypotheses reaches xi in one step and then gives equality, not strict descent. Part (c) also requests a point in an empty interval once x_n=xi. Preserve these claims and specify the corrected termination convention later.
- `R05E25`: The hypotheses allow M=0, but part (d) divides by A=M/(2*delta). A=0 must be separated or the displayed estimate reformulated.
- `R06E18`: The displayed formula for gamma_3 contains 1/t although the domain includes t=0. No endpoint value is printed. The continuous extension gamma_3(0)=1 must be stated explicitly before treating it as a curve.
- `R09E19`: The meaning of can be solved needs a local solution-branch interpretation. Eliminating x,y,z forces u(u-3)=0, so the full solution set has distinct branches and is not a single globally unique graph in x, y, or z. Fix the branch convention explicitly.
- `R09E31`: The stated hypothesis permits a nonzero singular semidefinite Hessian. For example, x^2+y^4 and x^2-y^4 at zero have the same quadratic Taylor polynomial but different local-minimum behavior. The original classification claim therefore needs qualification; no proof or counterexample is verified here.
- `R10E09`: The displayed iterated bounds are 0..a then 0..2pi, but the differentials are dr dtheta, which pairs the bounds with the wrong variables under usual iterated-integral notation. Preserve this source discrepancy and specify the intended order explicitly.
- `R10E09`: The hint removes the positive y-axis segment, whereas the interior parameter rectangle has its angular seam on the positive x-axis. The direct application of the stated branch of T needs a compatible slit or a changed angular interval.
- `R10E10`: As in Exercise 9, the printed bounds and differential order do not match under standard iterated-integral notation; the intended angular/radial order must be stated.
- `R10E22`: Part (c) requires the surface to avoid zero, since zeta is defined only on R^3 minus zero. g>0 alone does not ensure this: all three h_i may vanish at the same s, even identically. Add an explicit nonvanishing condition only in a separately marked correction.
- `R10E23`: Part (d) asks to extend some assertions without specifying which ones, so its final coverage scope must be selected and documented.
- `R10E23`: Part (c) needs an explicit n>=2 restriction or a convention for exactness of 0-forms when n=1; the chapter defines exactness via a (k-1)-form.
- `R11E11`: As literally a space of functions, L1 with the displayed distance is only a pseudometric space. The metric-space conclusion requires identification almost everywhere, as used elsewhere in the chapter; confirm and document that convention rather than asserting pointwise separation.

## Validation limits

Source inventory is not proof completion. A verified count requires source-to-type review, compilation, and the axiom audit. Full-plan completion and clean-checkout validation have not been established by this table.

See `mathlib-coverage.md` for representation gaps and `errata.md` for source corrections.
