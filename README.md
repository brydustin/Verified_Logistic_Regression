# Verified logistic regression (Isabelle/HOL)

Machine-checked facts about L2-regularised logistic regression and fixed-step gradient
descent on it, built on `HOL-Higher_Diff` (gradients `∇`, Hessians `∇²`) over HOL-Analysis
vectors `real^'n`, bridged to the AFP's first-order-methods library.  No locales, no `sorry`.

## Contents

| Theory | What it proves |
|---|---|
| `Smooth_Strongly_Convex` | For `f :: real^'n ⇒ real` with `μ‖d‖² ≤ dᵀ∇²f(x)d ≤ L‖d‖²` everywhere (`hess_bounds f μ L`): the quadratic upper and lower bounds (`quad_upper`, `quad_lower`) from the one-variable Taylor theorem along a segment; one gradient step with `0 < α ≤ 1/L` decreases `f` by `α/2‖∇f‖²` (`gd_step_decrease`); the Polyak–Łojasiewicz inequality (`pl_inequality`); a stationary point is the global minimizer (`stationary_is_min`); the linear rate `f(x_k) − f(x*) ≤ (1 − αμ)^k (f(x_0) − f(x*))` (`gd_linear_rate`), the iterate bound (`gd_iterate_distance`), and existence of the minimizer over any closed nonempty set and over the whole space (`strongly_convex_minimizer_exists_on`, `strongly_convex_minimizer_exists`, `gd_linear_rate_minimizer`). |
| `Logistic_Loss` | `sigmoid`, `softplus` and their derivatives; the loss `logistic_loss X y λ w = (1/m) Σ_k [softplus(x_kᵀw) − y_k x_kᵀw] + λ/2 ‖w‖²`; its gradient in closed form (`logistic_loss_grad`), its Hessian in closed form (`logistic_loss_hess`, `(1/m) Σ σ'(x_kᵀw) x_k x_kᵀ + λI`); the bounds `λ‖d‖² ≤ dᵀ∇²L d ≤ (R²/4 + λ)‖d‖²` when every row satisfies `‖x_k‖ ≤ R` (`logistic_hess_bounds`); and the resulting gradient-descent rate `(1 − αλ)^k` for `0 < α ≤ 1/(R²/4 + λ)` (`logistic_gd_rate`), with the step written out as `w − α ∇L(w)` (`logistic_gd_step`); and the same with the minimizer's existence built in (`logistic_gd_rate_minimizer`). |
| `Hessian_To_First_Order` | Bridge to the AFP entry [Projected_Gradient_Descent](https://isa-afp.org/entries/Projected_Gradient_Descent.html) (Lyu, 2026): `hess_bounds f μ L` with `μ ≥ 0` yields that entry's certificates `has_gradient_on`, `smooth_upper_bound_on L`, `strong_convex_lower_bound_on μ`, `convex_on`, and `strongly_smooth_convex_on L μ` on any convex set (`hess_bounds_strongly_smooth_convex_on`), with the sharp constants the entry otherwise assumes. For the logistic loss: `logistic_strongly_smooth_convex_on`, and as payoff `logistic_projected_gd_linear_rate`, the entry's linear rates for projected gradient descent over any closed convex weight set. The constrained minimizer exists (`strongly_convex_global_min_on`, from the generic theory's `strongly_convex_minimizer_exists_on`), so `logistic_projected_gd_linear_rate_minimizer` needs no minimizer hypothesis at all. |

Conventions: data `X :: real^'n^'m` with rows `X $ k` as samples, labels `y :: real^'m`
(0/1 in the classification reading; the analysis uses nothing about them), `CARD('m)` samples.

Existence of the minimizer is proved too: `strongly_convex_minimizer_exists_on` for any closed
nonempty set (coercivity from the lower quadratic bound, then `continuous_attains_inf` on the
intersection with a closed ball), its whole-space form `strongly_convex_minimizer_exists`,
`minimizer_stationary` (via `has_derivative_local_min`), and the hypothesis-free rate theorems
`gd_linear_rate_minimizer` / `logistic_gd_rate_minimizer`, which produce the minimizer `w*`
with `∇L(w*) = 0`, `L(w*) ≤ L(w)` for all `w`, and the `(1 − αλ)^k` rate.

## Not yet done

- Any statement about floating-point evaluation.  Everything here is over the reals.

## Building

Needs Isabelle2025-2, the `HOL-Higher_Diff` session (`~/Desktop/Higher_Diff`) and the AFP
entry `Projected_Gradient_Descent` (newer than the April 2026 AFP release; a copy is kept at
`~/Desktop/Isabelle/afp_extra/Projected_Gradient_Descent`):

```sh
isabelle build -d ~/Desktop/Higher_Diff -d ~/Desktop/Isabelle/afp_extra/Projected_Gradient_Descent -d . Logistic_Regression
```

`tools/chk.sh` runs that build and prints only the error lines.  For a fast single-theory
check (about 20 s) use `isabelle eval_at -l HOL-Higher_Diff -d ~/Desktop/Higher_Diff
Logistic_Loss.thy <line>`; without `-l` the tool tries to derive the logic from `ROOT` and
hangs on a broken session.

## License and citation

BSD 3-Clause, see `LICENSE`.  Citation metadata is in `CITATION.cff` (GitHub's "Cite this
repository" button reads it); in plain text:

```
Dustin Bryant. Verified logistic regression in Isabelle/HOL. 2026.
https://github.com/brydustin/Verified_Logistic_Regression
```

The AFP entry `Projected_Gradient_Descent` (Feier Lyu, 2026) that the bridge theory builds
on is not included here.
