theory Hessian_To_First_Order
  imports Logistic_Loss "Projected_Gradient_Descent.Main_Results"
begin

text \<open>Bridge from the Hessian bounds of \<open>Smooth_Strongly_Convex\<close> to the first-order certificates of
the AFP entry \<open>Projected_Gradient_Descent\<close> (Lyu, 2026).  That entry takes the certificates as
hypotheses; here they are derived from \<open>\<mu> \<parallel>d\<parallel>\<^sup>2 \<le> d\<^sup>T \<nabla>\<^sup>2 f x d \<le> L \<parallel>d\<parallel>\<^sup>2\<close>, with the sharp
constants.  Everything of the entry (projected gradient descent, residual rates, \<open>O(1/N)\<close> bounds)
then applies to any \<open>hess_bounds\<close> function, in particular to the logistic loss.\<close>

section \<open>Gradient and the two quadratic certificates\<close>

lemma hess_bounds_has_gradient_on:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "hess_bounds f \<mu> L"
  shows "has_gradient_on f UNIV (\<nabla> f)"
  unfolding has_gradient_on_def has_gradient_def
  using hess_boundsD(1) [OF assms] unfolding gderiv_def by blast

lemma hess_bounds_smooth_upper_bound_on:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and L: "0 \<le> L"
  shows "smooth_upper_bound_on L UNIV f (\<nabla> f)"
proof (rule smooth_upper_bound_onI [OF L])
  fix x y :: "real^'n"
  have "f (x + (y - x)) \<le> f x + (y - x) \<bullet> \<nabla> f x + L / 2 * ((y - x) \<bullet> (y - x))"
    by (rule quad_upper [OF hb])
  then show "f y \<le> f x + inner (\<nabla> f x) (y - x) + L / 2 * norm (y - x) ^ 2"
    by (simp add: inner_commute dot_square_norm)
qed

lemma hess_bounds_strong_convex_lower_bound_on:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 \<le> \<mu>"
  shows "strong_convex_lower_bound_on \<mu> UNIV f (\<nabla> f)"
proof (rule strong_convex_lower_bound_onI [OF \<mu>])
  fix x y :: "real^'n"
  have "f x + (y - x) \<bullet> \<nabla> f x + \<mu> / 2 * ((y - x) \<bullet> (y - x)) \<le> f (x + (y - x))"
    by (rule quad_lower [OF hb])
  then show "f x + inner (\<nabla> f x) (y - x) + \<mu> / 2 * norm (y - x) ^ 2 \<le> f y"
    by (simp add: inner_commute dot_square_norm)
qed

section \<open>Convexity from the lower certificate\<close>

lemma hess_bounds_convex_on:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 \<le> \<mu>"
  shows "convex_on UNIV f"
proof (rule convex_onI)
  show "convex (UNIV :: (real^'n) set)" by simp
  fix t :: real and x y :: "real^'n"
  assume t: "0 < t" "t < 1"
  let ?z = "(1 - t) *\<^sub>R x + t *\<^sub>R y"
  let ?g = "\<nabla> f ?z"
  have nonneg: "0 \<le> \<mu> / 2 * (d \<bullet> d)" for d :: "real^'n"
    using \<mu> by (intro mult_nonneg_nonneg inner_ge_zero) simp
  have A: "f ?z + (x - ?z) \<bullet> ?g \<le> f x"
    using quad_lower [OF hb, of ?z "x - ?z"] nonneg [of "x - ?z"] by simp
  have B: "f ?z + (y - ?z) \<bullet> ?g \<le> f y"
    using quad_lower [OF hb, of ?z "y - ?z"] nonneg [of "y - ?z"] by simp
  have A': "(1 - t) * f ?z + (1 - t) * ((x - ?z) \<bullet> ?g) \<le> (1 - t) * f x"
    using mult_left_mono [OF A, of "1 - t"] t by (simp add: distrib_left)
  have B': "t * f ?z + t * ((y - ?z) \<bullet> ?g) \<le> t * f y"
    using mult_left_mono [OF B, of t] t by (simp add: distrib_left)
  have vec0: "(1 - t) *\<^sub>R (x - ?z) + t *\<^sub>R (y - ?z) = 0"
    by (simp add: vec_eq_iff algebra_simps)
  have key: "(1 - t) * ((x - ?z) \<bullet> ?g) + t * ((y - ?z) \<bullet> ?g) = 0"
    using vec0 by (metis inner_add_left inner_scaleR_left inner_zero_left)
  have "(1 - t) * f ?z + t * f ?z = f ?z" by (simp add: algebra_simps)
  with A' B' key show "f ?z \<le> (1 - t) * f x + t * f y" by linarith
qed

section \<open>The combined certificate\<close>

theorem hess_bounds_strongly_smooth_convex_on:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 \<le> \<mu>"
  shows "strongly_smooth_convex_on L \<mu> UNIV f (\<nabla> f)"
proof (rule strongly_smooth_convex_onI)
  have L: "0 \<le> L" using hess_bounds_mu_le_L [OF hb] \<mu> by linarith
  show "smooth_convex_on L UNIV f (\<nabla> f)"
    by (rule smooth_convex_onI [OF convex_differentiable_onI
          [OF hess_bounds_convex_on [OF hb \<mu>] hess_bounds_has_gradient_on [OF hb]]
          hess_bounds_smooth_upper_bound_on [OF hb L]])
  show "strong_convex_lower_bound_on \<mu> UNIV f (\<nabla> f)"
    by (rule hess_bounds_strong_convex_lower_bound_on [OF hb \<mu>])
qed

corollary hess_bounds_strongly_smooth_convex_on_subset:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "hess_bounds f \<mu> L" and "0 \<le> \<mu>" and "convex C"
  shows "strongly_smooth_convex_on L \<mu> C f (\<nabla> f)"
  by (rule strongly_smooth_convex_on_subset
        [OF hess_bounds_strongly_smooth_convex_on [OF assms(1,2)] subset_UNIV assms(3)])

text \<open>Our iterate function is an instance of the entry's iterate predicate.\<close>

lemma gd_iter_gradient_descent_iterates:
  "gradient_descent_iterates \<alpha> (\<nabla> f) (gd_iter f \<alpha> x0)"
  unfolding gradient_descent_iterates_def
  by (simp add: gd_iter_Suc gd_step_def gradient_step_def)

section \<open>The logistic loss as a first-order certificate\<close>

theorem logistic_strongly_smooth_convex_on:
  fixes X :: "real^'n^'m"
  assumes R: "\<And>k. norm (X $ k) \<le> R" and lam: "0 \<le> lam" and C: "convex C"
  shows "strongly_smooth_convex_on (R\<^sup>2 / 4 + lam) lam C (logistic_loss X y lam) (logistic_grad X y lam)"
proof -
  have "\<nabla> (logistic_loss X y lam) = logistic_grad X y lam"
    by (rule ext) (rule logistic_loss_grad)
  with hess_bounds_strongly_smooth_convex_on_subset [OF logistic_hess_bounds [OF R lam, where y = y] lam C]
  show ?thesis by simp
qed

text \<open>Payoff: projected gradient descent for logistic regression over any closed convex set of
weights, with the entry's linear rates, for free.\<close>

theorem logistic_projected_gd_linear_rate:
  fixes X :: "real^'n^'m" and C :: "(real^'n) set"
  assumes R: "\<And>k. norm (X $ k) \<le> R" and lam: "0 < lam"
    and C: "closed C" "convex C"
    and pgd: "projected_gradient_descent_iterates C \<alpha> (logistic_grad X y lam) w"
    and w0: "w 0 \<in> C"
    and \<alpha>: "0 < \<alpha>" "\<alpha> * (R\<^sup>2 / 4 + lam) \<le> 1"
    and min: "global_min_on C (logistic_loss X y lam) ws"
  shows "norm (w N - ws) ^ 2 \<le> (1 / (1 + \<alpha> * lam)) ^ N * norm (w 0 - ws) ^ 2"
    and "0 < N \<Longrightarrow> logistic_loss X y lam (w N) - logistic_loss X y lam ws
           \<le> (1 / (1 + \<alpha> * lam)) ^ (N - 1) * norm (w 0 - ws) ^ 2 / (2 * \<alpha>)"
proof -
  have cert: "strongly_smooth_convex_on (R\<^sup>2 / 4 + lam) lam C (logistic_loss X y lam) (logistic_grad X y lam)"
    by (rule logistic_strongly_smooth_convex_on [OF R less_imp_le [OF lam] C(2)])
  show "norm (w N - ws) ^ 2 \<le> (1 / (1 + \<alpha> * lam)) ^ N * norm (w 0 - ws) ^ 2"
    using projected_gradient_descent_distance_sq_linear_rate [OF cert C pgd w0 \<alpha> min]
    by (simp add: projected_gradient_linear_rate_factor_def inverse_eq_divide)
  show "0 < N \<Longrightarrow> logistic_loss X y lam (w N) - logistic_loss X y lam ws
           \<le> (1 / (1 + \<alpha> * lam)) ^ (N - 1) * norm (w 0 - ws) ^ 2 / (2 * \<alpha>)"
    using projected_gradient_descent_function_value_linear_rate [OF cert C pgd w0 \<alpha> min]
    by (simp add: projected_gradient_linear_rate_factor_def inverse_eq_divide)
qed

section \<open>Existence of the constrained minimizer\<close>

text \<open>The entry's hypothesis \<open>global_min_on C f xs\<close> is a theorem for \<open>hess_bounds\<close> functions on any
closed nonempty \<open>C\<close> (\<open>strongly_convex_minimizer_exists_on\<close> in \<open>Smooth_Strongly_Convex\<close>).\<close>

theorem strongly_convex_global_min_on:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 < \<mu>" and C: "closed C" "C \<noteq> {}"
  obtains xs where "global_min_on C f xs"
proof -
  obtain xs where "xs \<in> C" "\<And>z. z \<in> C \<Longrightarrow> f xs \<le> f z"
    by (rule strongly_convex_minimizer_exists_on [OF hb \<mu> C]) (rule that; assumption)
  then have "global_min_on C f xs" unfolding global_min_on_def by blast
  then show thesis by (rule that)
qed

theorem logistic_projected_gd_linear_rate_minimizer:
  fixes X :: "real^'n^'m" and C :: "(real^'n) set"
  assumes R: "\<And>k. norm (X $ k) \<le> R" and lam: "0 < lam"
    and C: "closed C" "convex C" "C \<noteq> {}"
    and pgd: "projected_gradient_descent_iterates C \<alpha> (logistic_grad X y lam) w"
    and w0: "w 0 \<in> C"
    and \<alpha>: "0 < \<alpha>" "\<alpha> * (R\<^sup>2 / 4 + lam) \<le> 1"
  obtains ws where "global_min_on C (logistic_loss X y lam) ws"
    and "\<And>N. norm (w N - ws) ^ 2 \<le> (1 / (1 + \<alpha> * lam)) ^ N * norm (w 0 - ws) ^ 2"
    and "\<And>N. 0 < N \<Longrightarrow> logistic_loss X y lam (w N) - logistic_loss X y lam ws
           \<le> (1 / (1 + \<alpha> * lam)) ^ (N - 1) * norm (w 0 - ws) ^ 2 / (2 * \<alpha>)"
proof -
  have hb: "hess_bounds (logistic_loss X y lam) lam (R\<^sup>2 / 4 + lam)"
    by (rule logistic_hess_bounds [OF R]) (use lam in simp)
  obtain ws where min: "global_min_on C (logistic_loss X y lam) ws"
    by (rule strongly_convex_global_min_on [OF hb lam C(1) C(3)]) (rule that; assumption)
  show thesis
    by (rule that [OF min logistic_projected_gd_linear_rate(1) [OF R lam C(1,2) pgd w0 \<alpha> min]
                       logistic_projected_gd_linear_rate(2) [OF R lam C(1,2) pgd w0 \<alpha> min]])
qed

end
