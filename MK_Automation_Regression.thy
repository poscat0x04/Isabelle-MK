theory MK_Automation_Regression
  imports MK
begin

text \<open>
  These lemmas deliberately use the default rule collections, without local
  unfolding or extra rules. Keep the method on each lemma: a proof by blast
  does not test whether the same statement simplifies with simp.
\<close>

section \<open>Membership normalization\<close>

lemma comprehension_auto:
  "x \<in> {y | P(y)} \<longleftrightarrow> Set(x) \<and> P(x)"
  by auto

lemma bounded_comprehension_simp:
  "x \<in> {y \<in> A | P(y)} \<longleftrightarrow> x \<in> A \<and> P(x)"
  by simp

lemma empty_membership_simp: "x \<notin> {}"
  by simp

lemma universe_membership_simp: "x \<in> \<bbbV> \<longleftrightarrow> Set(x)"
  by simp

lemma inter_membership_simp:
  "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B"
  by simp

lemma union_membership_simp:
  "x \<in> A \<union> B \<longleftrightarrow> x \<in> A \<or> x \<in> B"
  by simp

lemma diff_membership_simp:
  "x \<in> A \\ B \<longleftrightarrow> x \<in> A \<and> x \<notin> B"
  by simp

lemma Union_membership_simp:
  "x \<in> \<Union>A \<longleftrightarrow> (\<exists>a \<in> A. x \<in> a)"
  by simp

lemma Inter_membership_simp:
  "x \<in> \<Inter>A \<longleftrightarrow> Set(x) \<and> (\<forall>a \<in> A. x \<in> a)"
  by simp

lemma power_membership_simp:
  "x \<in> \<P>(A) \<longleftrightarrow> Set(x) \<and> x \<subseteq> A"
  by simp

lemma member_is_set_simp: "x \<in> A \<Longrightarrow> Set(x)"
  by simp

lemma nested_membership_auto:
  "x \<in> (A \<union> B) \\ C \<longleftrightarrow> x \<in> (A \\ C) \<union> (B \\ C)"
  by auto

lemma nested_membership_blast:
  "x \<in> (A \<union> B) \\ C \<longleftrightarrow> x \<in> (A \\ C) \<union> (B \\ C)"
  by blast

section \<open>Proper-class guards\<close>

lemma proper_class_not_member:
  "PClass(x) \<Longrightarrow> x \<notin> A"
  by auto

lemma proper_class_not_in_power:
  "PClass(x) \<Longrightarrow> x \<notin> \<P>(A)"
  by simp

lemma proper_class_not_in_empty_intersection:
  "PClass(x) \<Longrightarrow> x \<notin> \<Inter>{}"
  by simp

lemma singleton_membership_guard:
  "x \<in> {a} \<longleftrightarrow> Set(x) \<and> x = a"
  by simp

lemma proper_class_singleton_empty:
  "PClass(a) \<Longrightarrow> {a} = {}"
  by simp

section \<open>Bounded quantifiers and subsets\<close>

lemma Ball_contrapositive_auto:
  "\<forall>x \<in> A. P(x) \<Longrightarrow> \<not>P(a) \<Longrightarrow> a \<notin> A"
  by auto

lemma Ball_contrapositive_blast:
  "\<forall>x \<in> A. P(x) \<Longrightarrow> \<not>P(a) \<Longrightarrow> a \<notin> A"
  by blast

lemma Ball_reuse_auto:
  "\<forall>x \<in> A. P(x) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> P(a) \<and> P(b)"
  by auto

lemma Ball_reuse_blast:
  "\<forall>x \<in> A. P(x) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> P(a) \<and> P(b)"
  by blast

lemma Ball_context_simp: "\<forall>x \<in> A. Set(x)"
  by simp

lemma Bexist_context_simp:
  "(\<exists>x \<in> A. Set(x) \<and> P(x)) \<longleftrightarrow> (\<exists>x \<in> A. P(x))"
  by simp

lemma empty_quantifiers_simp:
  "\<forall>x \<in> {}. P(x)"
  "\<not>(\<exists>x \<in> {}. P(x))"
  by simp_all

lemma singleton_quantifiers_simp:
  "(\<forall>x \<in> {a}. P(x)) \<longleftrightarrow> (Set(a) \<longrightarrow> P(a))"
  "(\<exists>x \<in> {a}. P(x)) \<longleftrightarrow> (Set(a) \<and> P(a))"
  by simp_all

lemma Bexist_one_point_simp:
  "(\<exists>x \<in> A. x = a) \<longleftrightarrow> a \<in> A"
  "(\<exists>x \<in> A. a = x) \<longleftrightarrow> a \<in> A"
  "(\<exists>x \<in> A. x = a \<and> P(x)) \<longleftrightarrow> a \<in> A \<and> P(a)"
  "(\<exists>x \<in> A. a = x \<and> P(x)) \<longleftrightarrow> a \<in> A \<and> P(a)"
  by simp_all

lemma subset_contrapositive_auto:
  "A \<subseteq> B \<Longrightarrow> x \<notin> B \<Longrightarrow> x \<notin> A"
  by auto

lemma subset_reuse_blast:
  "A \<subseteq> B \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<in> B \<and> y \<in> B"
  by blast

lemma subset_bounds_simp:
  "A \<subseteq> A"
  "{} \<subseteq> A"
  "A \<subseteq> \<bbbV>"
  "A \<subseteq> {} \<longleftrightarrow> A = {}"
  by simp_all

lemma class_algebra_auto:
  "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by auto

lemma class_algebra_blast:
  "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by blast

section \<open>Set construction and functions\<close>

lemma empty_set_simp: "Set({})"
  by simp

lemma nested_sets_simp:
  "Set(a) \<Longrightarrow> Set(b) \<Longrightarrow> Set(\<P>(a \<union> {b}))"
  by simp

lemma nested_sets_auto:
  "Set(a) \<Longrightarrow> Set(b) \<Longrightarrow> Set(\<P>(a \<union> {b}))"
  by auto

lemma nested_sets_blast:
  "Set(a) \<Longrightarrow> Set(b) \<Longrightarrow> Set(\<P>(a \<union> {b}))"
  by blast

lemma separation_set_simp:
  "Set(A) \<Longrightarrow> Set({x \<in> A | P(x)})"
  by simp

lemma pair_set_simp:
  "Set(a) \<Longrightarrow> Set(b) \<Longrightarrow> Set(\<langle>a,b\<rangle>)"
  by simp

lemma conditional_set_simp:
  "Set(a) \<Longrightarrow> Set(b) \<Longrightarrow> Set(if P then {a} else \<P>(b))"
  by simp

lemma pair_projections_simp:
  "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> fst(\<langle>a,b\<rangle>) = a"
  "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> snd(\<langle>a,b\<rangle>) = b"
  by simp_all

lemma lambda_application_simp:
  "a \<in> A \<Longrightarrow> (\<lambda>x \<in> A. {x})`a = {a}"
  by simp

lemma lambda_domain_simp: "dom(\<lambda>x \<in> A. {x}) = A"
  by simp

lemma proper_class_entry_dropped:
  "PClass(a) \<Longrightarrow> {a, b} = {b}"
  by auto

lemma proper_class_singleton_is_set:
  "PClass(a) \<Longrightarrow> Set({a})"
  by simp

section \<open>Lambda and relation automation\<close>

lemma lambda_is_function_auto: "Fun(\<lambda>x \<in> A. {x})"
  by auto

lemma lambda_pair_membership_simp:
  "Set(a) \<Longrightarrow> \<langle>a,{a}\<rangle> \<in> (\<lambda>x \<in> A. {x}) \<longleftrightarrow> a \<in> A"
  by simp

lemma lambda_range_simp:
  "y \<in> rng(\<lambda>x \<in> A. {x}) \<longleftrightarrow> (\<exists>x \<in> A. y = {x})"
  by simp

lemma application_is_set_simp:
  "Fun(f) \<Longrightarrow> x \<in> dom(f) \<Longrightarrow> Set(f`x)"
  by simp

lemma function_pair_membership_simp:
  "Fun(f) \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow>
    \<langle>x,y\<rangle> \<in> f \<longleftrightarrow> x \<in> dom(f) \<and> y = f`x"
  by simp

lemma conditional_singleton_auto:
  "x \<in> (if P then {a} else {}) \<longleftrightarrow> P \<and> Set(x) \<and> x = a"
  by auto

lemma inverse_composition_is_relation_auto: "Rel((P \<circ> Q)\<inverse>)"
  by auto

lemma inverse_membership_simp:
  "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow>
    \<langle>x,y\<rangle> \<in> R\<inverse> \<longleftrightarrow> \<langle>y,x\<rangle> \<in> R"
  by simp

lemma composition_witness_auto:
  "Set(x) \<Longrightarrow> Set(y) \<Longrightarrow> Set(z) \<Longrightarrow>
    \<langle>x,y\<rangle> \<in> R \<Longrightarrow> \<langle>y,z\<rangle> \<in> P \<Longrightarrow>
    \<langle>x,z\<rangle> \<in> P \<circ> R"
  by auto

lemma composition_of_singletons_auto:
  "Set(x) \<Longrightarrow> Set(y) \<Longrightarrow> Set(z) \<Longrightarrow>
    \<langle>x,z\<rangle> \<in> {\<langle>y,z\<rangle>} \<circ> {\<langle>x,y\<rangle>}"
  by auto

lemma proper_class_not_in_lambda_range:
  "PClass(y) \<Longrightarrow> y \<notin> rng(\<lambda>x \<in> A. {x})"
  by auto

end
