theory Logistic_Loss
  imports Smooth_Strongly_Convex
begin

text \<open>L2-regularised logistic regression: the loss, its gradient and Hessian in closed form,
uniform bounds on the Hessian, and the linear rate of fixed-step gradient descent.\<close>

section \<open>The logistic function\<close>

definition sigmoid :: "real \<Rightarrow> real" where
  "sigmoid z = 1 / (1 + exp (- z))"

definition softplus :: "real \<Rightarrow> real" where
  "softplus z = ln (1 + exp z)"

lemma one_plus_exp_pos: "0 < 1 + exp (z::real)"
  using exp_gt_zero [of z] by linarith

lemma sigmoid_alt: "sigmoid z = exp z / (1 + exp z)"
proof -
  have *: "exp z * (1 + exp (- z)) = 1 + exp z"
    by (simp add: algebra_simps mult_exp_exp)
  have "sigmoid z = (exp z * 1) / (exp z * (1 + exp (- z)))"
    unfolding sigmoid_def by (subst mult_divide_mult_cancel_left) simp_all
  then show ?thesis using * by simp
qed

lemma sigmoid_pos: "0 < sigmoid z"
  unfolding sigmoid_alt using one_plus_exp_pos [of z] by (simp add: divide_pos_pos)

lemma sigmoid_less_one: "sigmoid z < 1"
  unfolding sigmoid_alt using one_plus_exp_pos [of z] by (simp add: divide_less_eq)

lemma sigmoid_deriv_nonneg: "0 \<le> sigmoid z * (1 - sigmoid z)"
  using sigmoid_pos [of z] sigmoid_less_one [of z] by (simp add: zero_le_mult_iff)

lemma sigmoid_deriv_bound: "sigmoid z * (1 - sigmoid z) \<le> 1 / 4"
proof -
  have "(sigmoid z - 1 / 2) * (sigmoid z - 1 / 2) = 1 / 4 - sigmoid z * (1 - sigmoid z)"
    by algebra
  then show ?thesis using zero_le_square [of "sigmoid z - 1 / 2"] by linarith
qed

lemma sigmoid_DERIV: "DERIV sigmoid z :> sigmoid z * (1 - sigmoid z)"
proof -
  let ?e = "exp (- z)"
  have pos: "0 < 1 + ?e" by (rule one_plus_exp_pos)
  have D: "DERIV (\<lambda>z. 1 / (1 + exp (- z))) z :> ?e / ((1 + ?e) * (1 + ?e))"
    using pos by (auto intro!: derivative_eq_intros)
  have eq: "?e / ((1 + ?e) * (1 + ?e)) = 1 / (1 + ?e) * (1 - 1 / (1 + ?e))"
    using pos by (simp add: field_simps)
  show ?thesis
    unfolding sigmoid_def [abs_def] by (rule D [unfolded eq])
qed

lemma sigmoid_has_derivative:
  "(sigmoid has_derivative (\<lambda>h. sigmoid z * (1 - sigmoid z) * h)) (at z)"
  using sigmoid_DERIV unfolding has_field_derivative_def by simp

lemma softplus_DERIV: "DERIV softplus z :> sigmoid z"
proof -
  have A: "DERIV (\<lambda>z. 1 + exp z) z :> exp z"
    by (auto intro!: derivative_eq_intros)
  have B: "DERIV ln (1 + exp z) :> 1 / (1 + exp z)"
    by (rule DERIV_ln_divide [OF one_plus_exp_pos])
  have "DERIV (\<lambda>z. ln (1 + exp z)) z :> 1 / (1 + exp z) * exp z"
    by (rule DERIV_chain2 [OF B A])
  then show ?thesis
    unfolding softplus_def [abs_def] sigmoid_alt by simp
qed

section \<open>Gradient rules\<close>

lemma GDERIV_inner_const: "GDERIV (\<lambda>w. a \<bullet> w) w :> a"
proof -
  have "((\<lambda>w. a \<bullet> w) has_derivative (\<lambda>h. a \<bullet> h)) (at w)"
    by (rule bounded_linear.has_derivative [OF bounded_linear_inner_right has_derivative_ident])
  then show ?thesis
    unfolding gderiv_def by (rule has_derivative_eq_rhs) (simp add: fun_eq_iff inner_commute)
qed

lemma GDERIV_const_mult: "GDERIV f x :> df \<Longrightarrow> GDERIV (\<lambda>x. c * f x) x :> c *\<^sub>R df"
  by (rule GDERIV_DERIV_compose [OF _ DERIV_cmult_Id])

lemma GDERIV_sum:
  assumes "\<And>k. k \<in> S \<Longrightarrow> GDERIV (f k) x :> D k"
  shows "GDERIV (\<lambda>x. \<Sum>k\<in>S. f k x) x :> (\<Sum>k\<in>S. D k)"
  unfolding gderiv_def inner_sum_right
  by (rule has_derivative_sum) (simp add: assms [unfolded gderiv_def])

lemma GDERIV_inner_self: "GDERIV (\<lambda>w. w \<bullet> w) w :> 2 *\<^sub>R w"
proof -
  have "((\<lambda>w. w \<bullet> w) has_derivative (\<lambda>h. w \<bullet> h + h \<bullet> w)) (at w)"
    by (rule has_derivative_inner [OF has_derivative_ident has_derivative_ident])
  then show ?thesis
    unfolding gderiv_def by (rule has_derivative_eq_rhs) (simp add: fun_eq_iff inner_commute)
qed

section \<open>The regularised logistic loss\<close>

text \<open>The rows \<open>X $ k\<close> are the samples and \<open>y $ k\<close> the labels (0 or 1 in the classification
reading; nothing below needs that), \<open>lam \<ge> 0\<close> the ridge weight, \<open>CARD('m)\<close> the sample count.\<close>

definition logistic_loss :: "real^'n^'m \<Rightarrow> real^'m \<Rightarrow> real \<Rightarrow> real^'n::finite \<Rightarrow> real" where
  "logistic_loss X y lam w =
     (\<Sum>k\<in>UNIV. softplus (X $ k \<bullet> w) - y $ k * (X $ k \<bullet> w)) / real CARD('m) + lam / 2 * (w \<bullet> w)"

definition logistic_grad :: "real^'n^'m \<Rightarrow> real^'m \<Rightarrow> real \<Rightarrow> real^'n::finite \<Rightarrow> real^'n" where
  "logistic_grad X y lam w =
     (\<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) - y $ k) *\<^sub>R X $ k) /\<^sub>R real CARD('m) + lam *\<^sub>R w"

definition logistic_hess :: "real^'n^'m \<Rightarrow> real \<Rightarrow> real^'n::finite \<Rightarrow> real^'n^'n" where
  "logistic_hess X lam w =
     (\<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w))) *\<^sub>R outer_prod (X $ k) (X $ k))
       /\<^sub>R real CARD('m) + lam *\<^sub>R mat 1"

subsection \<open>Gradient\<close>

lemma logistic_term_GDERIV:
  "GDERIV (\<lambda>w. softplus (a \<bullet> w) - c * (a \<bullet> w)) w :> (sigmoid (a \<bullet> w) - c) *\<^sub>R a"
proof -
  have A: "GDERIV (\<lambda>w. softplus (a \<bullet> w)) w :> sigmoid (a \<bullet> w) *\<^sub>R a"
    by (rule GDERIV_DERIV_compose [OF GDERIV_inner_const softplus_DERIV])
  have B: "GDERIV (\<lambda>w. c * (a \<bullet> w)) w :> c *\<^sub>R a"
    by (rule GDERIV_const_mult [OF GDERIV_inner_const])
  show ?thesis
    by (rule GDERIV_subst [OF GDERIV_diff [OF A B]]) (simp add: scaleR_left_diff_distrib)
qed

lemma logistic_loss_GDERIV:
  fixes X :: "real^'n^'m"
  shows "GDERIV (logistic_loss X y lam) w :> logistic_grad X y lam w"
proof -
  let ?m = "real CARD('m)"
  have eq: "logistic_loss X y lam =
    (\<lambda>w. (1 / ?m) * (\<Sum>k\<in>UNIV. softplus (X $ k \<bullet> w) - y $ k * (X $ k \<bullet> w)) + (lam / 2) * (w \<bullet> w))"
    by (simp add: logistic_loss_def fun_eq_iff)
  have 1: "GDERIV (\<lambda>w. \<Sum>k\<in>UNIV. softplus (X $ k \<bullet> w) - y $ k * (X $ k \<bullet> w)) w
             :> (\<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) - y $ k) *\<^sub>R X $ k)"
    by (rule GDERIV_sum) (rule logistic_term_GDERIV)
  have 2: "GDERIV (\<lambda>w. (1 / ?m) * (\<Sum>k\<in>UNIV. softplus (X $ k \<bullet> w) - y $ k * (X $ k \<bullet> w))) w
             :> (1 / ?m) *\<^sub>R (\<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) - y $ k) *\<^sub>R X $ k)"
    by (rule GDERIV_const_mult [OF 1])
  have 3: "GDERIV (\<lambda>w. (lam / 2) * (w \<bullet> w)) w :> (lam / 2) *\<^sub>R (2 *\<^sub>R w)"
    by (rule GDERIV_const_mult [OF GDERIV_inner_self])
  show ?thesis
    unfolding eq logistic_grad_def
    by (rule GDERIV_subst [OF GDERIV_add [OF 2 3]]) (simp add: inverse_eq_divide)
qed

theorem logistic_loss_grad: "\<nabla> (logistic_loss X y lam) w = logistic_grad X y lam w"
  by (rule grad_fun_eq [OF logistic_loss_GDERIV])

subsection \<open>Hessian\<close>

lemma matrix_vector_mult_sum: "(\<Sum>k\<in>S. A k) *v v = (\<Sum>k\<in>S. A k *v v)"
  by (induct S rule: infinite_finite_induct) (simp_all add: matrix_vector_mult_add_rdistrib)

lemma scaleR_matrix_vector_mult:
  fixes A :: "real^'m^'n"
  shows "(c *\<^sub>R A) *v v = c *\<^sub>R (A *v v)"
  by (rule scaleR_matrix_vector_assoc [symmetric])

lemma logistic_hess_mult_vec:
  fixes X :: "real^'n^'m"
  shows "logistic_hess X lam w *v v =
     (\<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> v)) *\<^sub>R X $ k)
       /\<^sub>R real CARD('m) + lam *\<^sub>R v"
  unfolding logistic_hess_def
  by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector_mult matrix_vector_mult_sum
                outer_prod_mult_vec)

lemma logistic_grad_has_derivative:
  fixes X :: "real^'n^'m"
  shows "(logistic_grad X y lam has_derivative (\<lambda>v. logistic_hess X lam w *v v)) (at w)"
proof -
  let ?m = "real CARD('m)"
  have one_term: "((\<lambda>w. (sigmoid (X $ k \<bullet> w) - y $ k) *\<^sub>R X $ k) has_derivative
               (\<lambda>v. (sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> v)) *\<^sub>R X $ k)) (at w)"
    for k
  proof -
    have i: "((\<lambda>w. X $ k \<bullet> w) has_derivative (\<lambda>v. X $ k \<bullet> v)) (at w)"
      by (rule bounded_linear.has_derivative [OF bounded_linear_inner_right has_derivative_ident])
    have s: "((\<lambda>w. sigmoid (X $ k \<bullet> w)) has_derivative
              (\<lambda>v. sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> v))) (at w)"
      using has_derivative_compose [OF i sigmoid_has_derivative] by simp
    have "((\<lambda>w. sigmoid (X $ k \<bullet> w) - y $ k) has_derivative
            (\<lambda>v. sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> v))) (at w)"
      using has_derivative_diff [OF s has_derivative_const] by simp
    then show ?thesis by (rule has_derivative_scaleR_left)
  qed
  have sum: "((\<lambda>w. \<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) - y $ k) *\<^sub>R X $ k) has_derivative
              (\<lambda>v. \<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> v)) *\<^sub>R X $ k)) (at w)"
    by (rule has_derivative_sum) (rule one_term)
  have A: "((\<lambda>w. (\<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) - y $ k) *\<^sub>R X $ k) /\<^sub>R ?m) has_derivative
            (\<lambda>v. (\<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> v)) *\<^sub>R X $ k) /\<^sub>R ?m)) (at w)"
    by (rule has_derivative_scaleR_right [OF sum])
  have B: "((\<lambda>w. lam *\<^sub>R w) has_derivative (\<lambda>v. lam *\<^sub>R v)) (at w)"
    by (rule has_derivative_scaleR_right [OF has_derivative_ident])
  have "(logistic_grad X y lam has_derivative
          (\<lambda>v. (\<Sum>k\<in>UNIV. (sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> v)) *\<^sub>R X $ k) /\<^sub>R ?m
               + lam *\<^sub>R v)) (at w)"
    unfolding logistic_grad_def [abs_def] by (rule has_derivative_add [OF A B])
  then show ?thesis unfolding logistic_hess_mult_vec .
qed

theorem logistic_loss_HESS: "HESS (logistic_loss X y lam) w :> logistic_hess X lam w"
  unfolding has_hessian_def
proof -
  have "\<nabla> (logistic_loss X y lam) = logistic_grad X y lam"
    by (rule ext) (rule logistic_loss_grad)
  then show "(\<nabla> (logistic_loss X y lam) has_derivative (\<lambda>v. logistic_hess X lam w *v v)) (at w)"
    using logistic_grad_has_derivative by simp
qed

theorem logistic_loss_hess: "\<nabla>\<^sup>2 (logistic_loss X y lam) w = logistic_hess X lam w"
  by (rule hess_fun_eq [OF logistic_loss_HESS])

subsection \<open>Hessian bounds\<close>

lemma logistic_hess_quad:
  fixes X :: "real^'n^'m"
  shows "d \<bullet> (logistic_hess X lam w *v d) =
     (\<Sum>k\<in>UNIV. sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> d)\<^sup>2) / real CARD('m)
     + lam * (d \<bullet> d)"
  unfolding logistic_hess_mult_vec power2_eq_square
  by (simp add: inner_add_right inner_scaleR_right inner_sum_right inner_commute inverse_eq_divide
                mult.assoc)

lemma logistic_hess_lower:
  fixes X :: "real^'n^'m"
  assumes "0 \<le> lam"
  shows "lam * (d \<bullet> d) \<le> d \<bullet> (logistic_hess X lam w *v d)"
proof -
  have "0 \<le> (\<Sum>k\<in>UNIV. sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> d)\<^sup>2) / real CARD('m)"
    by (intro divide_nonneg_nonneg sum_nonneg mult_nonneg_nonneg sigmoid_deriv_nonneg) simp_all
  then show ?thesis unfolding logistic_hess_quad by simp
qed

lemma logistic_hess_upper:
  fixes X :: "real^'n^'m"
  assumes R: "\<And>k. norm (X $ k) \<le> R" and lam: "0 \<le> lam"
  shows "d \<bullet> (logistic_hess X lam w *v d) \<le> (R\<^sup>2 / 4 + lam) * (d \<bullet> d)"
proof -
  let ?m = "real CARD('m)"
  have mpos: "0 < ?m" by simp
  have one_term: "sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> d)\<^sup>2 \<le> R\<^sup>2 / 4 * (d \<bullet> d)" for k
  proof -
    have cs: "(X $ k \<bullet> d)\<^sup>2 \<le> (X $ k \<bullet> X $ k) * (d \<bullet> d)" by (rule Cauchy_Schwarz_ineq)
    have "X $ k \<bullet> X $ k = (norm (X $ k))\<^sup>2" by (simp add: dot_square_norm)
    also have "\<dots> \<le> R\<^sup>2" using R [of k] norm_ge_zero by (intro power_mono) auto
    finally have "(X $ k \<bullet> X $ k) * (d \<bullet> d) \<le> R\<^sup>2 * (d \<bullet> d)"
      by (rule mult_right_mono [OF _ inner_ge_zero])
    with cs have q: "(X $ k \<bullet> d)\<^sup>2 \<le> R\<^sup>2 * (d \<bullet> d)" by linarith
    have "sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> d)\<^sup>2 \<le> 1 / 4 * (R\<^sup>2 * (d \<bullet> d))"
      by (rule mult_mono [OF sigmoid_deriv_bound q]) simp_all
    then show ?thesis by simp
  qed
  have "(\<Sum>k\<in>UNIV. sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> d)\<^sup>2)
          \<le> of_nat (card (UNIV :: 'm set)) * (R\<^sup>2 / 4 * (d \<bullet> d))"
    by (rule sum_bounded_above) (rule one_term)
  then have *: "(\<Sum>k\<in>UNIV. sigmoid (X $ k \<bullet> w) * (1 - sigmoid (X $ k \<bullet> w)) * (X $ k \<bullet> d)\<^sup>2) / ?m
                  \<le> R\<^sup>2 / 4 * (d \<bullet> d)"
    using mpos by (simp add: pos_divide_le_eq mult.commute)
  have "(R\<^sup>2 / 4 + lam) * (d \<bullet> d) = R\<^sup>2 / 4 * (d \<bullet> d) + lam * (d \<bullet> d)"
    by (simp add: distrib_right)
  with * show ?thesis unfolding logistic_hess_quad by linarith
qed

theorem logistic_hess_bounds:
  fixes X :: "real^'n^'m"
  assumes R: "\<And>k. norm (X $ k) \<le> R" and lam: "0 \<le> lam"
  shows "hess_bounds (logistic_loss X y lam) lam (R\<^sup>2 / 4 + lam)"
  unfolding hess_bounds_def
proof (intro conjI allI)
  fix x :: "real^'n"
  show "GDERIV (logistic_loss X y lam) x :> \<nabla> (logistic_loss X y lam) x"
    unfolding logistic_loss_grad by (rule logistic_loss_GDERIV)
  show "HESS (logistic_loss X y lam) x :> \<nabla>\<^sup>2 (logistic_loss X y lam) x"
    unfolding logistic_loss_hess by (rule logistic_loss_HESS)
next
  fix x d :: "real^'n"
  show "lam * (d \<bullet> d) \<le> d \<bullet> (\<nabla>\<^sup>2 (logistic_loss X y lam) x *v d)"
    unfolding logistic_loss_hess by (rule logistic_hess_lower [OF lam])
  show "d \<bullet> (\<nabla>\<^sup>2 (logistic_loss X y lam) x *v d) \<le> (R\<^sup>2 / 4 + lam) * (d \<bullet> d)"
    unfolding logistic_loss_hess by (rule logistic_hess_upper [OF R lam])
qed

section \<open>Gradient descent on the logistic loss\<close>

lemma logistic_gd_step:
  "gd_step (logistic_loss X y lam) \<alpha> w = w - \<alpha> *\<^sub>R logistic_grad X y lam w"
  by (simp add: gd_step_def logistic_loss_grad)

theorem logistic_gd_rate:
  fixes X :: "real^'n^'m"
  assumes R: "\<And>k. norm (X $ k) \<le> R" and lam: "0 < lam"
    and \<alpha>: "0 < \<alpha>" "\<alpha> \<le> 1 / (R\<^sup>2 / 4 + lam)"
    and st: "logistic_grad X y lam ws = 0"
  shows "logistic_loss X y lam (gd_iter (logistic_loss X y lam) \<alpha> w0 k) - logistic_loss X y lam ws
           \<le> (1 - \<alpha> * lam) ^ k * (logistic_loss X y lam w0 - logistic_loss X y lam ws)"
proof (rule gd_linear_rate)
  show "hess_bounds (logistic_loss X y lam) lam (R\<^sup>2 / 4 + lam)"
    by (rule logistic_hess_bounds [OF R]) (use lam in simp)
  show "\<nabla> (logistic_loss X y lam) ws = 0"
    unfolding logistic_loss_grad by (rule st)
qed (use lam \<alpha> in simp_all)

end
