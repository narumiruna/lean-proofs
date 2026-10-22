# Rudin progress

Generated from `exercises.json`. Do not edit counts by hand.

| Chapter | Verified resolutions | As stated | Refuted/corrected | Verified obligations |
| --- | --- | --- | --- | --- |
| 1 | 20/20 | 19 | 1 | 55/55 |
| 2 | 30/30 | 29 | 1 | 71/71 |
| 3 | 25/25 | 24 | 1 | 89/89 |
| 4 | 26/26 | 26 | 0 | 74/74 |
| 5 | 29/29 | 27 | 2 | 84/84 |
| 6 | 1/19 | 1 | 0 | 2/54 |
| 7 | 0/26 | 0 | 0 | 0/79 |
| 8 | 0/31 | 0 | 0 | 0/79 |
| 9 | 1/31 | 1 | 0 | 1/110 |
| 10 | 0/32 | 0 | 0 | 0/117 |
| 11 | 2/18 | 1 | 1 | 5/37 |

Total: **134/287 verified resolutions**; **381/849 obligations** verified.

These comprise 128 exercises proved as stated and 6 false source claims resolved by counterexamples and explicit corrections. A refuted claim is not counted as a proved original statement.

## Source issues and blockers

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
