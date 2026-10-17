theory Smooth_Strongly_Convex
  imports "HOL-Higher_Diff.Higher_Diffs"
begin

text \<open>Quadratic upper and lower bounds for a twice differentiable \<open>f :: real^'n \<Rightarrow> real\<close> whose
Hessian quadratic form lies between \<open>\<mu> \<parallel>d\<parallel>\<^sup>2\<close> and \<open>L \<parallel>d\<parallel>\<^sup>2\<close>, and the linear rate of fixed-step
gradient descent that follows.  Everything comes from the one-variable Taylor theorem applied
along the segment.\<close>

section \<open>Derivatives along a line\<close>

lemma DERIV_along_line:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "GDERIV f (x + t *\<^sub>R d) :> g"
  shows "DERIV (\<lambda>t. f (x + t *\<^sub>R d)) t :> d \<bullet> g"
proof -
  have 1: "((\<lambda>t. x + t *\<^sub>R d) has_derivative (\<lambda>h. h *\<^sub>R d)) (at t)"
    by (auto intro!: derivative_eq_intros)
  have 2: "(f has_derivative (\<lambda>h. h \<bullet> g)) (at (x + t *\<^sub>R d))"
    using assms unfolding gderiv_def by simp
  have "((\<lambda>t. f (x + t *\<^sub>R d)) has_derivative (\<lambda>h. (h *\<^sub>R d) \<bullet> g)) (at t)"
    using has_derivative_compose [OF 1 2] by simp
  then show ?thesis
    unfolding has_field_derivative_def
    by (rule has_derivative_eq_rhs) (simp add: fun_eq_iff inner_scaleR_left mult.commute)
qed

lemma DERIV_grad_along_line:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "HESS f (x + t *\<^sub>R d) :> H"
  shows "DERIV (\<lambda>t. d \<bullet> \<nabla> f (x + t *\<^sub>R d)) t :> d \<bullet> (H *v d)"
proof -
  have 1: "((\<lambda>t. x + t *\<^sub>R d) has_derivative (\<lambda>h. h *\<^sub>R d)) (at t)"
    by (auto intro!: derivative_eq_intros)
  have 2: "(\<nabla> f has_derivative (\<lambda>v. H *v v)) (at (x + t *\<^sub>R d))"
    using assms unfolding has_hessian_def .
  have 3: "((\<lambda>t. \<nabla> f (x + t *\<^sub>R d)) has_derivative (\<lambda>h. H *v (h *\<^sub>R d))) (at t)"
    using has_derivative_compose [OF 1 2] by simp
  have "((\<lambda>t. d \<bullet> \<nabla> f (x + t *\<^sub>R d)) has_derivative (\<lambda>h. d \<bullet> (H *v (h *\<^sub>R d)))) (at t)"
    by (rule bounded_linear.has_derivative [OF bounded_linear_inner_right 3])
  then show ?thesis
    unfolding has_field_derivative_def
    by (rule has_derivative_eq_rhs)
       (simp add: fun_eq_iff matrix_vector_mult_scaleR inner_scaleR_right mult.commute)
qed

section \<open>Taylor's theorem along a segment\<close>

lemma taylor_segment:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes G: "\<And>z. GDERIV f z :> \<nabla> f z" and H: "\<And>z. HESS f z :> \<nabla>\<^sup>2 f z"
  obtains t where "0 < t" "t < 1"
    "f (x + d) = f x + d \<bullet> \<nabla> f x + (d \<bullet> (\<nabla>\<^sup>2 f (x + t *\<^sub>R d) *v d)) / 2"
proof -
  define D where "D = (\<lambda>m t. if m = (0::nat) then f (x + t *\<^sub>R d)
                              else if m = 1 then d \<bullet> \<nabla> f (x + t *\<^sub>R d)
                              else d \<bullet> (\<nabla>\<^sup>2 f (x + t *\<^sub>R d) *v d))"
  have deriv: "\<forall>m t. m < 2 \<and> 0 \<le> t \<and> t \<le> 1 \<longrightarrow> DERIV (D m) t :> D (Suc m) t"
  proof (intro allI impI)
    fix m :: nat and t :: real
    assume "m < 2 \<and> 0 \<le> t \<and> t \<le> 1"
    then consider "m = 0" | "m = 1" by linarith
    then show "DERIV (D m) t :> D (Suc m) t"
    proof cases
      case 1
      then show ?thesis unfolding D_def using DERIV_along_line [OF G] by simp
    next
      case 2
      then show ?thesis unfolding D_def using DERIV_grad_along_line [OF H] by simp
    qed
  qed
  have D0: "D 0 = (\<lambda>t. f (x + t *\<^sub>R d))"
    by (simp add: D_def)
  have "\<exists>t::real. 0 < t \<and> t < 1 \<and>
      (\<lambda>t. f (x + t *\<^sub>R d)) 1 = (\<Sum>m<2. D m 0 / fact m * (1 - 0)^m) + D 2 t / fact 2 * (1 - 0)^2"
    by (rule Taylor_up [where diff = D and a = 0]) (use deriv D0 in auto)
  then obtain t where t: "0 < t" "t < 1"
    and eq: "f (x + d) = (\<Sum>m<2. D m 0 / fact m * (1 - 0)^m) + D 2 t / fact 2 * (1 - 0)^2"
    by auto
  have "(\<Sum>m<2. D m 0 / fact m * (1 - 0)^m) = f x + d \<bullet> \<nabla> f x"
    by (simp add: numeral_2_eq_2 D_def)
  moreover have "D 2 t / fact 2 * (1 - 0)^2 = (d \<bullet> (\<nabla>\<^sup>2 f (x + t *\<^sub>R d) *v d)) / 2"
    by (simp add: D_def numeral_2_eq_2)
  ultimately have "f (x + d) = f x + d \<bullet> \<nabla> f x + (d \<bullet> (\<nabla>\<^sup>2 f (x + t *\<^sub>R d) *v d)) / 2"
    using eq by simp
  with t show thesis by (rule that)
qed

section \<open>Uniform Hessian bounds\<close>

text \<open>\<open>hess_bounds f \<mu> L\<close>: \<open>f\<close> has a gradient and a Hessian everywhere, and
\<open>\<mu> \<parallel>d\<parallel>\<^sup>2 \<le> d\<^sup>T \<nabla>\<^sup>2 f x d \<le> L \<parallel>d\<parallel>\<^sup>2\<close> at every point.\<close>

definition hess_bounds :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "hess_bounds f \<mu> L \<longleftrightarrow>
     (\<forall>x. GDERIV f x :> \<nabla> f x) \<and> (\<forall>x. HESS f x :> \<nabla>\<^sup>2 f x) \<and>
     (\<forall>x d. \<mu> * (d \<bullet> d) \<le> d \<bullet> (\<nabla>\<^sup>2 f x *v d) \<and> d \<bullet> (\<nabla>\<^sup>2 f x *v d) \<le> L * (d \<bullet> d))"

lemma hess_boundsD:
  assumes "hess_bounds f \<mu> L"
  shows "GDERIV f x :> \<nabla> f x" "HESS f x :> \<nabla>\<^sup>2 f x"
    "\<mu> * (d \<bullet> d) \<le> d \<bullet> (\<nabla>\<^sup>2 f x *v d)" "d \<bullet> (\<nabla>\<^sup>2 f x *v d) \<le> L * (d \<bullet> d)"
  using assms unfolding hess_bounds_def by blast+

lemma quad_upper:
  assumes "hess_bounds f \<mu> L"
  shows "f (x + d) \<le> f x + d \<bullet> \<nabla> f x + L / 2 * (d \<bullet> d)"
proof -
  obtain t where eq: "f (x + d) = f x + d \<bullet> \<nabla> f x + (d \<bullet> (\<nabla>\<^sup>2 f (x + t *\<^sub>R d) *v d)) / 2"
    using taylor_segment [OF hess_boundsD(1,2) [OF assms]] by blast
  have "d \<bullet> (\<nabla>\<^sup>2 f (x + t *\<^sub>R d) *v d) \<le> L * (d \<bullet> d)"
    by (rule hess_boundsD [OF assms])
  with eq show ?thesis by simp
qed

lemma quad_lower:
  assumes "hess_bounds f \<mu> L"
  shows "f x + d \<bullet> \<nabla> f x + \<mu> / 2 * (d \<bullet> d) \<le> f (x + d)"
proof -
  obtain t where eq: "f (x + d) = f x + d \<bullet> \<nabla> f x + (d \<bullet> (\<nabla>\<^sup>2 f (x + t *\<^sub>R d) *v d)) / 2"
    using taylor_segment [OF hess_boundsD(1,2) [OF assms]] by blast
  have "\<mu> * (d \<bullet> d) \<le> d \<bullet> (\<nabla>\<^sup>2 f (x + t *\<^sub>R d) *v d)"
    by (rule hess_boundsD [OF assms])
  with eq show ?thesis by simp
qed

lemma hess_bounds_mu_le_L:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "hess_bounds f \<mu> L"
  shows "\<mu> \<le> L"
proof -
  let ?d = "vec 1 :: real^'n"
  have "?d \<noteq> 0" by (simp add: vec_eq_iff)
  then have pos: "0 < ?d \<bullet> ?d" by (simp add: inner_gt_zero_iff)
  have "\<mu> * (?d \<bullet> ?d) \<le> L * (?d \<bullet> ?d)"
    by (rule order_trans [OF hess_boundsD(3) hess_boundsD(4)]) (rule assms)+
  with pos show ?thesis by (simp add: mult_right_le_imp_le)
qed

section \<open>Consequences for gradient descent\<close>

definition gd_step :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n" where
  "gd_step f \<alpha> x = x - \<alpha> *\<^sub>R \<nabla> f x"

definition gd_iter :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> nat \<Rightarrow> real^'n" where
  "gd_iter f \<alpha> x0 k = (gd_step f \<alpha> ^^ k) x0"

lemma gd_iter_0 [simp]: "gd_iter f \<alpha> x0 0 = x0"
  by (simp add: gd_iter_def)

lemma gd_iter_Suc: "gd_iter f \<alpha> x0 (Suc k) = gd_step f \<alpha> (gd_iter f \<alpha> x0 k)"
  by (simp add: gd_iter_def)

text \<open>One gradient step with \<open>0 < \<alpha> \<le> 1/L\<close> decreases \<open>f\<close> by at least \<open>\<alpha>/2 \<parallel>\<nabla>f x\<parallel>\<^sup>2\<close>.\<close>

lemma gd_step_decrease:
  assumes hb: "hess_bounds f \<mu> L" and \<alpha>: "0 < \<alpha>" "\<alpha> \<le> 1 / L"
  shows "f (gd_step f \<alpha> x) \<le> f x - \<alpha> / 2 * (\<nabla> f x \<bullet> \<nabla> f x)"
proof -
  let ?g = "\<nabla> f x"
  have Lpos: "0 < L"
  proof (rule ccontr)
    assume "\<not> 0 < L"
    then have "1 / L \<le> 0" by (simp add: divide_nonpos_neg divide_le_0_iff)
    with \<alpha> show False by linarith
  qed
  have \<alpha>L: "\<alpha> * L \<le> 1"
    using \<alpha>(2) Lpos by (simp add: pos_le_divide_eq mult.commute)
  have gg: "0 \<le> ?g \<bullet> ?g" by (rule inner_ge_zero)
  have "f (x + (- \<alpha>) *\<^sub>R ?g) \<le> f x + ((- \<alpha>) *\<^sub>R ?g) \<bullet> ?g + L / 2 * (((- \<alpha>) *\<^sub>R ?g) \<bullet> ((- \<alpha>) *\<^sub>R ?g))"
    by (rule quad_upper [OF hb])
  also have "\<dots> = f x - \<alpha> * (?g \<bullet> ?g) + L / 2 * \<alpha>\<^sup>2 * (?g \<bullet> ?g)"
    by (simp add: inner_scaleR_left inner_scaleR_right power2_eq_square algebra_simps)
  also have "\<dots> \<le> f x - \<alpha> * (?g \<bullet> ?g) + \<alpha> / 2 * (?g \<bullet> ?g)"
  proof -
    have "L / 2 * \<alpha>\<^sup>2 = \<alpha> / 2 * (\<alpha> * L)" by (simp add: power2_eq_square)
    also have "\<dots> \<le> \<alpha> / 2"
      using \<alpha>L \<alpha>(1) by (intro mult_left_le) simp_all
    finally have "L / 2 * \<alpha>\<^sup>2 * (?g \<bullet> ?g) \<le> \<alpha> / 2 * (?g \<bullet> ?g)"
      by (rule mult_right_mono [OF _ gg])
    then show ?thesis by linarith
  qed
  finally show ?thesis
    by (simp add: gd_step_def scaleR_minus_left algebra_simps)
qed

text \<open>Strong convexity gives the Polyak--\L{}ojasiewicz inequality: the gradient at \<open>x\<close> bounds how
far \<open>f x\<close> can be above any other value.\<close>

lemma complete_square_bound:
  fixes a b c \<mu> :: real
  assumes "0 < \<mu>" and "0 \<le> a + 2 / \<mu> * b + (1 / \<mu>)\<^sup>2 * c"
  shows "- c / (2 * \<mu>) \<le> b + \<mu> / 2 * a"
proof -
  have "0 \<le> \<mu> / 2 * (a + 2 / \<mu> * b + (1 / \<mu>)\<^sup>2 * c)"
    using assms by (intro mult_nonneg_nonneg) simp_all
  also have "\<dots> = \<mu> / 2 * a + b + c / (2 * \<mu>)"
    using assms(1) by (simp add: field_simps power2_eq_square)
  finally show ?thesis by simp
qed

lemma pl_inequality:
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 < \<mu>"
  shows "f x - f z \<le> (\<nabla> f x \<bullet> \<nabla> f x) / (2 * \<mu>)"
proof -
  let ?g = "\<nabla> f x"
  define d where "d = z - x"
  have lower: "f x + d \<bullet> ?g + \<mu> / 2 * (d \<bullet> d) \<le> f z"
    using quad_lower [OF hb, of x d] by (simp add: d_def)
  have "0 \<le> (d + (1 / \<mu>) *\<^sub>R ?g) \<bullet> (d + (1 / \<mu>) *\<^sub>R ?g)" by (rule inner_ge_zero)
  also have "\<dots> = d \<bullet> d + 2 / \<mu> * (d \<bullet> ?g) + (1 / \<mu>)\<^sup>2 * (?g \<bullet> ?g)"
    using \<mu> by (simp add: inner_add_left inner_add_right inner_scaleR_left inner_scaleR_right
                  inner_commute [of ?g d] power2_eq_square field_simps)
  finally have "- (?g \<bullet> ?g) / (2 * \<mu>) \<le> d \<bullet> ?g + \<mu> / 2 * (d \<bullet> d)"
    by (rule complete_square_bound [OF \<mu>])
  with lower show ?thesis by simp
qed

text \<open>A stationary point of a strongly convex function is its unique global minimizer.\<close>

lemma stationary_is_min:
  assumes hb: "hess_bounds f \<mu> L" and st: "\<nabla> f xs = 0"
  shows "f xs + \<mu> / 2 * ((z - xs) \<bullet> (z - xs)) \<le> f z"
  using quad_lower [OF hb, of xs "z - xs"] st by simp

section \<open>Existence of the minimizer\<close>

text \<open>Strong convexity makes \<open>f\<close> coercive: outside the ball of radius \<open>2\<parallel>\<nabla>f 0\<parallel>/\<mu>\<close> it is
at least \<open>f 0\<close>, so the minimum over that compact ball is the global minimum.\<close>

lemma strongly_convex_outside_ball:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 < \<mu>" and z: "2 * norm (\<nabla> f 0) / \<mu> \<le> norm z"
  shows "f 0 \<le> f z"
proof -
  let ?g = "\<nabla> f 0"
  have lower: "f 0 + z \<bullet> ?g + \<mu> / 2 * (z \<bullet> z) \<le> f z"
    using quad_lower [OF hb, of 0 z] by simp
  have cs: "- (norm z * norm ?g) \<le> z \<bullet> ?g"
    using Cauchy_Schwarz_ineq2 [of z ?g] unfolding abs_le_iff by linarith
  have zz: "z \<bullet> z = norm z * norm z"
    by (simp add: dot_square_norm power2_eq_square)
  have "2 * norm ?g \<le> \<mu> * norm z"
    using z \<mu> by (simp add: pos_divide_le_eq mult.commute)
  then have "norm ?g \<le> \<mu> / 2 * norm z" by (simp add: field_simps)
  then have nonneg: "0 \<le> norm z * (\<mu> / 2 * norm z - norm ?g)"
    by (intro mult_nonneg_nonneg norm_ge_zero) simp
  have id: "norm z * (\<mu> / 2 * norm z - norm ?g) = \<mu> / 2 * (norm z * norm z) - norm z * norm ?g"
    by algebra
  show ?thesis using lower cs nonneg id unfolding zz by linarith
qed

theorem strongly_convex_minimizer_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 < \<mu>"
  obtains xs where "\<And>z. f xs \<le> f z"
proof -
  let ?r = "2 * norm (\<nabla> f 0) / \<mu>"
  let ?B = "cball (0::real^'n) ?r"
  have "isCont f x" for x
    using hess_boundsD(1) [OF hb, of x] unfolding gderiv_def by (rule has_derivative_continuous)
  then have cont: "continuous_on ?B f"
    by (simp add: continuous_at_imp_continuous_on)
  have "0 \<le> ?r" using \<mu> by (simp add: divide_nonneg_pos)
  then have zero_in: "0 \<in> ?B" by simp
  then have "?B \<noteq> {}" by blast
  obtain xs where xs: "xs \<in> ?B" "\<forall>y\<in>?B. f xs \<le> f y"
    using continuous_attains_inf [OF compact_cball \<open>?B \<noteq> {}\<close> cont] by blast
  have "f xs \<le> f z" for z
  proof (cases "z \<in> ?B")
    case True
    then show ?thesis using xs by blast
  next
    case False
    then have "\<not> norm z \<le> ?r" by (simp add: mem_cball dist_norm)
    then have "?r \<le> norm z" by linarith
    then have "f 0 \<le> f z" by (rule strongly_convex_outside_ball [OF hb \<mu>])
    moreover have "f xs \<le> f 0" using xs zero_in by blast
    ultimately show ?thesis by linarith
  qed
  then show thesis by (rule that)
qed

lemma minimizer_stationary:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and min: "\<And>z. f xs \<le> f z"
  shows "\<nabla> f xs = 0"
proof -
  have "(f has_derivative (\<lambda>h. h \<bullet> \<nabla> f xs)) (at xs)"
    using hess_boundsD(1) [OF hb] unfolding gderiv_def .
  moreover have "eventually (\<lambda>y. f xs \<le> f y) (at xs)"
    by (simp add: min)
  ultimately have "(\<lambda>h. h \<bullet> \<nabla> f xs) = (\<lambda>h. 0)"
    by (rule has_derivative_local_min)
  from fun_cong [OF this, of "\<nabla> f xs"] have "\<nabla> f xs \<bullet> \<nabla> f xs = 0" by simp
  then show ?thesis by simp
qed

theorem gd_linear_rate:
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 < \<mu>"
    and \<alpha>: "0 < \<alpha>" "\<alpha> \<le> 1 / L" and st: "\<nabla> f xs = 0"
  shows "f (gd_iter f \<alpha> x0 k) - f xs \<le> (1 - \<alpha> * \<mu>) ^ k * (f x0 - f xs)"
proof -
  have Lpos: "0 < L" using hess_bounds_mu_le_L [OF hb] \<mu> by linarith
  have "\<alpha> * \<mu> \<le> \<alpha> * L" using hess_bounds_mu_le_L [OF hb] \<alpha>(1) by (simp add: mult_left_mono)
  also have "\<dots> \<le> 1" using \<alpha>(2) Lpos by (simp add: pos_le_divide_eq mult.commute)
  finally have rate_nonneg: "0 \<le> 1 - \<alpha> * \<mu>" by simp
  show ?thesis
  proof (induction k)
    case 0
    show ?case by simp
  next
    case (Suc k)
    let ?x = "gd_iter f \<alpha> x0 k"
    let ?g = "\<nabla> f ?x"
    have step: "f (gd_step f \<alpha> ?x) \<le> f ?x - \<alpha> / 2 * (?g \<bullet> ?g)"
      by (rule gd_step_decrease [OF hb \<alpha>])
    have "f ?x - f xs \<le> (?g \<bullet> ?g) / (2 * \<mu>)"
      by (rule pl_inequality [OF hb \<mu>])
    then have "\<alpha> * \<mu> * (f ?x - f xs) \<le> \<alpha> * \<mu> * ((?g \<bullet> ?g) / (2 * \<mu>))"
      using \<alpha>(1) \<mu> by (intro mult_left_mono) simp_all
    also have "\<dots> = \<alpha> / 2 * (?g \<bullet> ?g)"
      using \<mu> by (simp add: field_simps)
    finally have pl: "\<alpha> * \<mu> * (f ?x - f xs) \<le> \<alpha> / 2 * (?g \<bullet> ?g)" .
    have "f (gd_iter f \<alpha> x0 (Suc k)) - f xs \<le> (1 - \<alpha> * \<mu>) * (f ?x - f xs)"
      using step pl unfolding gd_iter_Suc by (simp add: algebra_simps)
    also have "\<dots> \<le> (1 - \<alpha> * \<mu>) * ((1 - \<alpha> * \<mu>) ^ k * (f x0 - f xs))"
      using Suc.IH rate_nonneg by (rule mult_left_mono)
    finally show ?case by simp
  qed
qed

corollary gd_iterate_distance:
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 < \<mu>"
    and \<alpha>: "0 < \<alpha>" "\<alpha> \<le> 1 / L" and st: "\<nabla> f xs = 0"
  shows "(gd_iter f \<alpha> x0 k - xs) \<bullet> (gd_iter f \<alpha> x0 k - xs)
           \<le> 2 / \<mu> * ((1 - \<alpha> * \<mu>) ^ k * (f x0 - f xs))"
proof -
  let ?x = "gd_iter f \<alpha> x0 k"
  have "\<mu> / 2 * ((?x - xs) \<bullet> (?x - xs)) \<le> f ?x - f xs"
    using stationary_is_min [OF hb st, of ?x] by simp
  also have "\<dots> \<le> (1 - \<alpha> * \<mu>) ^ k * (f x0 - f xs)"
    by (rule gd_linear_rate [OF hb \<mu> \<alpha> st])
  finally show ?thesis
    using \<mu> by (simp add: field_simps)
qed

text \<open>The rate theorem without the stationary-point hypothesis: the minimizer exists.\<close>

theorem gd_linear_rate_minimizer:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes hb: "hess_bounds f \<mu> L" and \<mu>: "0 < \<mu>" and \<alpha>: "0 < \<alpha>" "\<alpha> \<le> 1 / L"
  obtains xs where "\<nabla> f xs = 0" "\<And>z. f xs \<le> f z"
    "\<And>k. f (gd_iter f \<alpha> x0 k) - f xs \<le> (1 - \<alpha> * \<mu>) ^ k * (f x0 - f xs)"
proof -
  obtain xs where min: "\<And>z. f xs \<le> f z"
    by (rule strongly_convex_minimizer_exists [OF hb \<mu>]) (rule that; assumption)
  have st: "\<nabla> f xs = 0" by (rule minimizer_stationary [OF hb min])
  show thesis by (rule that [OF st min gd_linear_rate [OF hb \<mu> \<alpha> st]])
qed

end
