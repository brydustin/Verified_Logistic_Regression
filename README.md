# Verified logistic regression (Isabelle/HOL)

Machine-checked facts about L2-regularised logistic regression and fixed-step gradient
descent on it, built on `HOL-Higher_Diff` (gradients `∇`, Hessians `∇²`) over HOL-Analysis
vectors `real^'n`.  No locales, no `sorry`.

## Contents

| Theory | What it proves |
|---|---|
| `Smooth_Strongly_Convex` | For `f :: real^'n ⇒ real` with `μ‖d‖² ≤ dᵀ∇²f(x)d ≤ L‖d‖²` everywhere (`hess_bounds f μ L`): the quadratic upper and lower bounds (`quad_upper`, `quad_lower`) from the one-variable Taylor theorem along a segment; one gradient step with `0 < α ≤ 1/L` decreases `f` by `α/2‖∇f‖²` (`gd_step_decrease`); the Polyak–Łojasiewicz inequality (`pl_inequality`); a stationary point is the global minimizer (`stationary_is_min`); the linear rate `f(x_k) − f(x*) ≤ (1 − αμ)^k (f(x_0) − f(x*))` (`gd_linear_rate`) and the iterate bound (`gd_iterate_distance`). |
| `Logistic_Loss` | `sigmoid`, `softplus` and their derivatives; the loss `logistic_loss X y λ w = (1/m) Σ_k [softplus(x_kᵀw) − y_k x_kᵀw] + λ/2 ‖w‖²`; its gradient in closed form (`logistic_loss_grad`), its Hessian in closed form (`logistic_loss_hess`, `(1/m) Σ σ'(x_kᵀw) x_k x_kᵀ + λI`); the bounds `λ‖d‖² ≤ dᵀ∇²L d ≤ (R²/4 + λ)‖d‖²` when every row satisfies `‖x_k‖ ≤ R` (`logistic_hess_bounds`); and the resulting gradient-descent rate `(1 − αλ)^k` for `0 < α ≤ 1/(R²/4 + λ)` (`logistic_gd_rate`), with the step written out as `w − α ∇L(w)` (`logistic_gd_step`). |

Conventions: data `X :: real^'n^'m` with rows `X $ k` as samples, labels `y :: real^'m`
(0/1 in the classification reading; the analysis uses nothing about them), `CARD('m)` samples.

## Not yet done

- Existence of the minimizer `w*` (the rate theorem assumes a stationary point; strong
  convexity makes it unique, and coercivity gives existence, but that argument is not yet
  formalized).
- Any statement about floating-point evaluation.  Everything here is over the reals.

## Building

Needs Isabelle2025-2 and the `HOL-Higher_Diff` session (`~/Desktop/Higher_Diff`):

```sh
isabelle build -d ~/Desktop/Higher_Diff -d . Logistic_Regression
```

`tools/chk.sh` runs that build and prints only the error lines.  For a fast single-theory
check (about 20 s) use `isabelle eval_at -l HOL-Higher_Diff -d ~/Desktop/Higher_Diff
Logistic_Loss.thy <line>`; without `-l` the tool tries to derive the logic from `ROOT` and
hangs on a broken session.
