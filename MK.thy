theory MK
  imports FOL
begin

declare [[eta_contract = false]]

typedecl i
instance i :: "term" ..

axiomatization
  mem :: "[i, i] \<Rightarrow> o" (infixl \<open>\<in>\<close> 50)
and
  ClassAbs :: "(i \<Rightarrow> o) \<Rightarrow> i"

definition Set :: "i \<Rightarrow> o"
  where
    "Set(x) \<equiv> \<exists>A. x \<in> A"

abbreviation PClass :: "i \<Rightarrow> o"
  where
    "PClass(x) \<equiv> \<not>Set(x)"

lemma SetI [intro, simp]: "x \<in> A \<Longrightarrow> Set(x)"
  unfolding Set_def by blast

text \<open>
  Set elimination is explicit: opening an arbitrary containing class is rarely
  useful in automatic search. Constructor rules below discharge sethood goals
  by reducing them to sethood of their arguments.
\<close>

lemma SetE: "Set(x) \<Longrightarrow> (\<And> A. x \<in> A \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Set_def by blast

axiomatization
where
  comprehension: "x \<in> ClassAbs(P) \<longleftrightarrow> Set(x) \<and> P(x)"

syntax
  "_ClassAbs" :: "[pttrn, o] \<Rightarrow> i"
    ("(\<open>indent=1 notation=\<open>mixfix class comprehension\<close>\<close>{_ |/ _})")

syntax_consts
  "_ClassAbs" \<rightleftharpoons> ClassAbs

translations
  "{x | P}" \<rightleftharpoons> "CONST ClassAbs (\<lambda>x. P)"

lemma classAbsI [intro]: "Set(x) \<Longrightarrow> P(x) \<Longrightarrow> x \<in> {x | P(x)}"
  unfolding comprehension by blast

lemma classAbsD [dest]:
  assumes "x \<in> {x | P(x)}"
  shows "Set(x)" "P(x)"
  using assms unfolding comprehension by blast+

lemma classAbsE [elim]:
  assumes "x \<in> {x | P(x)}"
  and "Set(x) \<Longrightarrow> P(x) \<Longrightarrow> R"
  shows "R"
  using assms unfolding comprehension by blast

syntax
  "_ClassAbsIn" :: "[pttrn, i, o] \<Rightarrow> i"
    ("(1{_ \<in> _ |/ _})")

syntax_consts
  "_ClassAbsIn" \<rightleftharpoons> ClassAbs

translations
  "{x \<in> A | P}" \<rightharpoonup> "{x | x \<in> A \<and> P}"

lemma bounded_classAbs_iff [simp]:
  "x \<in> {y \<in> A | P(y)} \<longleftrightarrow> x \<in> A \<and> P(x)"
  by blast

text \<open>
  Keep unrestricted comprehension out of the default simpset. Expanding nested
  replacement comprehensions can obscure witnesses needed by automatic proofs.
  Use \<open>simp add: comprehension\<close> explicitly when that expansion is wanted.
  The specialized membership rules retain any necessary \<open>Set\<close> guards.
\<close>

text \<open>
  The syntax category \<open>args\<close> is inherited from Pure and represents
  a nonempty comma-separated list of terms. Enumeration expands directly to
  class comprehension: \<open>{a, b, c}\<close> means
  \<open>{x | x = a \<or> x = b \<or> x = c}\<close>, with a fresh bound variable.
\<close>

syntax
  "_FinSet" :: "args \<Rightarrow> i" (\<open>(\<open>indent=1 notation=\<open>mixfix set enumeration\<close>\<close>{_})\<close>)

syntax_consts
  "_FinSet" \<rightleftharpoons> ClassAbs

text \<open>
  Replacement binds a space-separated list in both the expression and the
  predicate: \<open>{t | x y. P}\<close> expands to
  \<open>{a | \<exists>x y. P \<and> a = t}\<close>.
  The output variable is introduced as a bound
  index, rather than a named variable, to avoid capturing free variables.
\<close>

syntax
  "_ClassReplace" :: "[i, idts, o] \<Rightarrow> i"
    ("(1{_ |/_./ _})")

syntax_consts
  "_ClassReplace" \<rightleftharpoons> ClassAbs

parse_translation \<open>
  let
    val ex_tr = snd (Syntax_Trans.mk_binder_tr ("EX ", \<^const_syntax>\<open>Ex\<close>));

    fun nvars (Const (\<^syntax_const>\<open>_idts\<close>, _) $ _ $ xs) = nvars xs + 1
      | nvars _ = 1;

    (* Lift existing loose indices before adding the ClassAbs abstraction. *)
    fun enum_eq t =
      Syntax.const \<^const_syntax>\<open>IFOL.eq\<close> $ Bound 0 $ incr_boundvars 1 t;

    fun enum_body (Const (\<^syntax_const>\<open>_args\<close>, _) $ t $ ts) =
          Syntax.const \<^const_syntax>\<open>IFOL.disj\<close> $ enum_eq t $ enum_body ts
      | enum_body t = enum_eq t;

    fun enumeration_tr _ [ts] =
          Syntax.const \<^const_syntax>\<open>ClassAbs\<close> $ absdummy dummyT (enum_body ts)
      | enumeration_tr _ ts = raise TERM ("class enumeration", ts);

    fun replacement_tr ctxt [t, idts, P] =
          let
            val n = nvars idts;
            (* Inside n existential binders, Bound n refers to the outer
               ClassAbs binder. mk_binder_tr abstracts idts in both t and P. *)
            val eq = Syntax.const \<^const_syntax>\<open>IFOL.eq\<close> $ Bound n $ t;
            val body = Syntax.const \<^const_syntax>\<open>IFOL.conj\<close> $ P $ eq;
          in Syntax.const \<^const_syntax>\<open>ClassAbs\<close> $
            absdummy dummyT (ex_tr ctxt [idts, body]) end
      | replacement_tr _ ts = raise TERM ("class replacement", ts);
  in
    [(\<^syntax_const>\<open>_FinSet\<close>, enumeration_tr),
     (\<^syntax_const>\<open>_ClassReplace\<close>, replacement_tr)]
  end
\<close>

print_translation \<open>
  let
    val ex_tr' = snd (Syntax_Trans.mk_binder_tr' (\<^const_syntax>\<open>Ex\<close>, "DUMMY"));

    (* Remove the ClassAbs binder only when no entry depends on it. *)
    fun enum_entry (Const (\<^const_syntax>\<open>IFOL.eq\<close>, _) $ Bound 0 $ t) =
          if loose_bvar1 (t, 0) then raise Match else incr_boundvars ~1 t
      | enum_entry _ = raise Match;

    fun enum_entries (Const (\<^const_syntax>\<open>IFOL.disj\<close>, _) $ P $ Q) =
          enum_entry P :: enum_entries Q
      | enum_entries P = [enum_entry P];

    fun enum_args [t] = t
      | enum_args (t :: ts) = Syntax.const \<^syntax_const>\<open>_args\<close> $ t $ enum_args ts
      | enum_args [] = raise Match;

    (* The hidden output variable must occur only on the left of the equality. *)
    fun check (Const (\<^const_syntax>\<open>Ex\<close>, _) $ Abs (_, _, body), n) =
          check (body, n + 1)
      | check (Const (\<^const_syntax>\<open>IFOL.conj\<close>, _) $ P $
          (Const (\<^const_syntax>\<open>IFOL.eq\<close>, _) $ Bound m $ t), n) =
          n > 0 andalso m = n andalso
          not (loose_bvar1 (P, n)) andalso not (loose_bvar1 (t, n))
      | check _ = false;

    fun class_tr' ctxt [Abs (abs as (_, _, body))] =
          (Syntax.const \<^syntax_const>\<open>_FinSet\<close> $ enum_args (enum_entries body)
          handle Match => if check (body, 0) then
            let
              val _ $ ex_abs = body;
              val _ $ idts $ (_ $ P $ (_ $ _ $ t)) = ex_tr' ctxt [ex_abs];
            in Syntax.const \<^syntax_const>\<open>_ClassReplace\<close> $ t $ idts $ P end
          else
            let
              val (x as _ $ Free (xN, _), P) = Syntax_Trans.atomic_abs_tr' ctxt abs;
              val plain = Syntax.const \<^syntax_const>\<open>_ClassAbs\<close> $ x $ P;
            in
              case P of
                Const (\<^const_syntax>\<open>IFOL.conj\<close>, _) $
                  (Const (\<^const_syntax>\<open>mem\<close>, _) $
                    (Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (yN, _)) $ A) $ Q =>
                  if xN = yN andalso
                    not (Term.exists_subterm (fn Free (z, _) => z = xN | _ => false) A)
                  then Syntax.const \<^syntax_const>\<open>_ClassAbsIn\<close> $ x $ A $ Q
                  else plain
              | _ => plain
            end)
      | class_tr' _ _ = raise Match;
  in [(\<^const_syntax>\<open>ClassAbs\<close>, class_tr')] end
\<close>

definition Ball :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where
    "Ball(A, P) \<equiv> \<forall> x. x \<in> A \<longrightarrow> P(x)"

definition Bexist :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where
    "Bexist(A, P) \<equiv> \<exists> x. x \<in> A \<and> P(x)"

syntax
  "_Ball" :: "[pttrn, i, o] \<Rightarrow> o" (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<in>\<close>\<close>\<forall>_\<in>_./ _)\<close> 10)
  "_Bexist" :: "[pttrn, i, o] \<Rightarrow> o" (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<in>\<close>\<close>\<exists>_\<in>_./ _)\<close> 10)

syntax_consts
  "_Ball" \<rightleftharpoons> Ball
and
  "_Bexist" \<rightleftharpoons> Bexist

translations
  "\<forall>x \<in> A. P" \<rightleftharpoons> "CONST Ball(A, \<lambda>x. P)"
  "\<exists>x \<in> A. P" \<rightleftharpoons> "CONST Bexist(A, \<lambda>x. P)"

lemma BallI [intro!]: "(\<And> x. x \<in> A \<Longrightarrow> P(x)) \<Longrightarrow> \<forall>x \<in> A. P(x)"
  unfolding Ball_def by blast

lemma BallD [dest]: "\<forall>x \<in> A. P(x) \<Longrightarrow> x \<in> A \<Longrightarrow> P(x)"
  unfolding Ball_def by blast

text \<open>
  The branching elimination rule supports contraposition. It stays unsafe
  because selecting an instance requires search; introduction and existential
  elimination have deterministic logical decompositions and are safe rules.
\<close>

lemma BallE [elim]:
  "\<forall>x \<in> A. P(x) \<Longrightarrow> (\<not>(x \<in> A) \<Longrightarrow> R) \<Longrightarrow> (P(x) \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Ball_def by blast

lemma BexistI [intro]: "x \<in> A \<Longrightarrow> P(x) \<Longrightarrow> \<exists>y \<in> A. P(y)"
  unfolding Bexist_def by blast

text \<open>The predicate can identify a witness before its domain is checked.\<close>

lemma Bexist_revI [intro]: "P(x) \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists>y \<in> A. P(y)"
  by (rule BexistI)

lemma BexistE [elim!]: "\<exists>x \<in> A. P(x) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P(x) \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Bexist_def by blast

lemma Ball_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow>
    (\<forall>x \<in> A. P(x)) \<longleftrightarrow> (\<forall>x \<in> B. Q(x))"
  unfolding Ball_def by blast

lemma Bexist_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow>
    (\<exists>x \<in> A. P(x)) \<longleftrightarrow> (\<exists>x \<in> B. Q(x))"
  unfolding Bexist_def by blast

lemma Ball_True [simp]: "\<forall>x \<in> A. True"
  by blast

lemma Bexist_False [simp]: "\<not>(\<exists>x \<in> A. False)"
  by blast

lemma Bexist_one_point [simp]:
  "(\<exists>x \<in> A. x = a) \<longleftrightarrow> a \<in> A"
  "(\<exists>x \<in> A. a = x) \<longleftrightarrow> a \<in> A"
  "(\<exists>x \<in> A. x = a \<and> P(x)) \<longleftrightarrow> a \<in> A \<and> P(a)"
  "(\<exists>x \<in> A. a = x \<and> P(x)) \<longleftrightarrow> a \<in> A \<and> P(a)"
  by blast+

(* The zero-width break separates ")" and "." as lexical delimiters, so
   applications such as B(x). remain usable in other binder domains. *)
syntax
  "_Sall" :: "[idts, o] \<Rightarrow> o"
    (\<open>(\<open>indent=3 notation=\<open>binder \<forall>Set\<close>\<close>\<forall>Set'(_')/./ _)\<close> 10)
  "_Sexist" :: "[idts, o] \<Rightarrow> o"
    (\<open>(\<open>indent=3 notation=\<open>binder \<exists>Set\<close>\<close>\<exists>Set'(_')/./ _)\<close> 10)

syntax_consts
  "_Sall" \<rightleftharpoons> All
and
  "_Sexist" \<rightleftharpoons> Ex

text \<open>
  Each variable has its own guard: \<open>\<forall>Set(x y). P\<close> expands to
  \<open>\<forall>x. Set(x) \<longrightarrow> (\<forall>y. Set(y) \<longrightarrow> P)\<close>.
  Existential binders use conjunction instead. Printing groups consecutive
  quantifiers with matching guards, preserving ordinary quantifiers between them.
\<close>

parse_translation \<open>
  let
    fun set_binder_tr quantifier connective =
      let
        val binder_tr = snd (Syntax_Trans.mk_binder_tr ("Set", quantifier));

        (* Insert the guard after abstraction, so even an anonymous binder
           refers to its own variable. Keep binder type constraints intact. *)
        fun guard (Abs (x, T, P)) =
              Abs (x, T, Syntax.const connective $
                (Syntax.const \<^const_syntax>\<open>Set\<close> $ Bound 0) $ P)
          | guard (Const ("_constrainAbs", T) $ abs $ typ) =
              Const ("_constrainAbs", T) $ guard abs $ typ
          | guard t = raise TERM ("Set binder abstraction", [t]);

        fun bind ctxt (Const (\<^syntax_const>\<open>_idts\<close>, _) $ x $ xs, P) =
              bind ctxt (x, bind ctxt (xs, P))
          | bind ctxt (x, P) =
              let val q $ abs = binder_tr ctxt [x, P]
              in q $ guard abs end;

        fun tr ctxt [xs, P] = bind ctxt (xs, P)
          | tr _ ts = raise TERM ("Set binder", ts);
      in tr end;
  in
    [(\<^syntax_const>\<open>_Sall\<close>,
        set_binder_tr \<^const_syntax>\<open>All\<close> \<^const_syntax>\<open>IFOL.imp\<close>),
     (\<^syntax_const>\<open>_Sexist\<close>,
        set_binder_tr \<^const_syntax>\<open>Ex\<close> \<^const_syntax>\<open>IFOL.conj\<close>)]
  end
\<close>

print_translation \<open>
  let
    fun idts [x] = x
      | idts (x :: xs) = Syntax.const \<^syntax_const>\<open>_idts\<close> $ x $ idts xs
      | idts [] = raise Match;

    fun set_binder_tr' quantifier connective bounded_syntax =
      let
        fun dest_guard (Const (c, _) $
              (Const (s, _) $ Bound 0) $ P) =
              if c = connective andalso s = \<^const_syntax>\<open>Set\<close>
              then P else raise Match
          | dest_guard _ = raise Match;

        fun collect ctxt bounded (x, T, body) =
          let
            val P =
              if bounded then dest_guard body
              else if can dest_guard body then raise Match else body;
            (* Opening one binder at a time preserves outer references and
               chooses names that cannot capture free variables. *)
            val (v, Q) =
              if Name.is_internal x andalso not (Term.is_dependent P) then
                (Const (\<^syntax_const>\<open>_idtdummy\<close>, T), incr_boundvars ~1 P)
              else Syntax_Trans.atomic_abs_tr' ctxt (Name.clean x, T, P);
            val (vs, R) =
              (case Q of
                Const (q, _) $ Abs abs =>
                  if q = quantifier then
                    (collect ctxt bounded abs handle Match => ([], Q))
                  else ([], Q)
              | _ => ([], Q));
          in (v :: vs, R) end;

        fun tr ctxt [Abs (abs as (_, _, body))] =
              let
                val bounded = can dest_guard body;
                val (vs, P) = collect ctxt bounded abs;
                val syn = if bounded then bounded_syntax else Mixfix.binder_name quantifier;
              in Syntax.const syn $ idts vs $ P end
          | tr _ _ = raise Match;
      in tr end;
  in
    [(\<^const_syntax>\<open>All\<close>,
        set_binder_tr' \<^const_syntax>\<open>All\<close> \<^const_syntax>\<open>IFOL.imp\<close>
          \<^syntax_const>\<open>_Sall\<close>),
     (\<^const_syntax>\<open>Ex\<close>,
        set_binder_tr' \<^const_syntax>\<open>Ex\<close> \<^const_syntax>\<open>IFOL.conj\<close>
          \<^syntax_const>\<open>_Sexist\<close>)]
  end
\<close>

abbreviation not_mem :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<notin>\<close> 50)
  where
    "A \<notin> B \<equiv> \<not> (A \<in> B)"

definition subset :: "[i, i] \<Rightarrow> o" (infixl \<open>\<subseteq>\<close> 50)
  where
    "A \<subseteq> B \<equiv> \<forall> x. x \<in> A \<longrightarrow> x \<in> B"

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  unfolding subset_def by blast

lemma subsetD [dest]: "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<in> B)"
  unfolding subset_def by auto

abbreviation empty :: "i" (\<open>\<emptyset>\<close>)
  where
    "\<emptyset> \<equiv> {x | False}"

notation (input) empty ("{}")

abbreviation universe :: "i" (\<open>\<bbbV>\<close>)
  where
    "\<bbbV> \<equiv> {x | True}"

lemma empty_iff [simp]: "x \<notin> {}"
  by blast

lemma universe_iff [simp]: "x \<in> \<bbbV> \<longleftrightarrow> Set(x)"
  by blast

lemma singleton_iff [simp]: "x \<in> {a} \<longleftrightarrow> Set(x) \<and> x = a"
  by blast

lemma empty_quantifiers [simp]:
  "\<forall>x \<in> {}. P(x)"
  "\<not>(\<exists>x \<in> {}. P(x))"
  by blast+

lemma singleton_quantifiers [simp]:
  "(\<forall>x \<in> {a}. P(x)) \<longleftrightarrow> (Set(a) \<longrightarrow> P(a))"
  "(\<exists>x \<in> {a}. P(x)) \<longleftrightarrow> (Set(a) \<and> P(a))"
  by blast+

lemma subset_refl [simp]: "A \<subseteq> A"
  by blast

lemma empty_subset [simp]: "{} \<subseteq> A"
  by blast

lemma subset_universe [simp]: "A \<subseteq> \<bbbV>"
  by blast

definition inter :: "[i, i] \<Rightarrow> i" (infixl \<open>\<inter>\<close> 70)
  where
    "A \<inter> B \<equiv> {x | x \<in> A \<and> x \<in> B }"

lemma interI [intro!]: "x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> (A \<inter> B)"
  unfolding inter_def by blast

lemma interE [elim!]: "x \<in> (A \<inter> B) \<Longrightarrow> (x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding inter_def by blast

lemma inter_iff [simp]: "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B"
  by blast

definition union :: "[i, i] \<Rightarrow> i" (infixl \<open>\<union>\<close> 65)
  where
    "A \<union> B \<equiv> {x | x \<in> A \<or> x \<in> B }"

lemma unionI1 [intro]: "x \<in> A \<Longrightarrow> x \<in> (A \<union> B)"
  unfolding union_def by blast

lemma unionI2 [intro]: "x \<in> B \<Longrightarrow> x \<in> (A \<union> B)"
  unfolding union_def by blast

lemma unionE [elim!]: "x \<in> (A \<union> B) \<Longrightarrow> (x \<in> A \<Longrightarrow> R) \<Longrightarrow> (x \<in> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding union_def by blast

lemma union_iff [simp]: "x \<in> A \<union> B \<longleftrightarrow> x \<in> A \<or> x \<in> B"
  by blast

definition diff :: "[i, i] \<Rightarrow> i" (infixl \<open>\\<close> 65)
  where
    "A \\ B \<equiv> {x | x \<in> A \<and> x \<notin> B}"

lemma diffI [intro!]: "x \<in> A \<and> x \<notin> B \<Longrightarrow> x \<in> (A \\ B)"
  unfolding diff_def by blast

lemma diffE [elim!]: "x \<in> (A \\ B) \<Longrightarrow> (x \<in> A \<Longrightarrow> x \<notin> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding diff_def by blast

lemma diff_iff [simp]: "x \<in> A \\ B \<longleftrightarrow> x \<in> A \<and> x \<notin> B"
  by blast

definition Inter :: "i \<Rightarrow> i" (\<open>(\<open>open_block notation=\<open>prefix \<Inter>\<close>\<close>\<Inter>_)\<close> [90] 90)
  where
    "\<Inter>A = {x | \<forall>a \<in> A. x \<in> a}"

lemma InterI [intro]: "Set(x) \<Longrightarrow> (\<And> a. a \<in> A \<Longrightarrow> x \<in> a) \<Longrightarrow> x \<in> \<Inter>A"
  unfolding Inter_def by blast

lemma InterD [dest]:"x \<in> \<Inter>A \<Longrightarrow> a \<in> A \<Longrightarrow> x \<in> a"
  unfolding Inter_def by blast

lemma Inter_iff [simp]:
  "x \<in> \<Inter>A \<longleftrightarrow> Set(x) \<and> (\<forall>a \<in> A. x \<in> a)"
  unfolding Inter_def by (rule comprehension)

definition Union :: "i \<Rightarrow> i" (\<open>(\<open>open_block notation=\<open>prefix \<Union>\<close>\<close>\<Union>_)\<close> [90] 90)
  where
    "\<Union>A = {x | \<exists>a \<in> A. x \<in> a}"

lemma UnionI [intro]: "x \<in> a \<Longrightarrow> a \<in> A \<Longrightarrow> x \<in> \<Union>A"
  unfolding Union_def by blast

lemma UnionE [elim!]: "x \<in> \<Union>A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<in> a \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Union_def by blast

lemma Union_iff [simp]: "x \<in> \<Union>A \<longleftrightarrow> (\<exists>a \<in> A. x \<in> a)"
  by blast

syntax
  "_UNION" :: "[pttrn, i, i] \<Rightarrow> i"  (\<open>(\<open>indent=3 notation=\<open>binder \<Union>\<in>\<close>\<close>\<Union>_\<in>_./_)\<close> 10)
  "_INTER" :: "[pttrn, i, i] \<Rightarrow> i"  (\<open>(\<open>indent=3 notation=\<open>binder \<Inter>\<in>\<close>\<close>\<Inter>_\<in>_./_)\<close> 10)
syntax_consts
  "_UNION" \<rightleftharpoons> Union and
  "_INTER" \<rightleftharpoons> Inter
parse_translation \<open>
  let
    val ex_tr = snd (Syntax_Trans.mk_binder_tr ("indexed class", \<^const_syntax>\<open>Ex\<close>));

    fun indexed_tr operator ctxt [x, A, B] =
          let
            (* A is outside the index binder; B is inside it. Both are lifted
               past the two new abstractions before introducing the guards. *)
            fun body (Abs (x, T, B)) =
                  Abs (x, T, Syntax.const \<^const_syntax>\<open>IFOL.conj\<close> $
                    (Syntax.const \<^const_syntax>\<open>mem\<close> $ Bound 0 $ incr_boundvars 2 A) $
                    (Syntax.const \<^const_syntax>\<open>IFOL.eq\<close> $ Bound 1 $ B))
              | body (Const ("_constrainAbs", T) $ abs $ typ) =
                  Const ("_constrainAbs", T) $ body abs $ typ
              | body t = raise TERM ("indexed class abstraction", [t]);
            val ex $ abs = ex_tr ctxt [x, incr_boundvars 2 B];
          in Syntax.const operator $
            (Syntax.const \<^const_syntax>\<open>ClassAbs\<close> $
              absdummy dummyT (ex $ body abs)) end
      | indexed_tr _ _ ts = raise TERM ("indexed class", ts);
  in
    [(\<^syntax_const>\<open>_UNION\<close>, indexed_tr \<^const_syntax>\<open>Union\<close>),
     (\<^syntax_const>\<open>_INTER\<close>, indexed_tr \<^const_syntax>\<open>Inter\<close>)]
  end
\<close>
print_translation \<open>
  let
    fun indexed_tr' syntax ctxt
          [Const (\<^const_syntax>\<open>ClassAbs\<close>, _) $
            Abs (_, _, Const (\<^const_syntax>\<open>Ex\<close>, _) $
              Abs (x, T, body as Const (\<^const_syntax>\<open>IFOL.conj\<close>, _) $
                (Const (\<^const_syntax>\<open>mem\<close>, _) $ Bound 0 $ A) $
                (Const (\<^const_syntax>\<open>IFOL.eq\<close>, _) $ Bound 1 $ B)))] =
          if loose_bvar1 (A, 0) orelse loose_bvar1 (A, 1) orelse loose_bvar1 (B, 1)
          then raise Match
          else
            let
              (* Remove the hidden output binder, then open the index binder
                 with a fresh name chosen against both A and B. *)
              val (x, _ $ (_ $ _ $ A) $ (_ $ _ $ B)) =
                Syntax_Trans.atomic_abs_tr' ctxt (Name.clean x, T, Term.incr_bv ~1 1 body);
            in Syntax.const syntax $ x $ A $ B end
      | indexed_tr' _ _ _ = raise Match;
  in
    [(\<^const_syntax>\<open>Union\<close>, indexed_tr' \<^syntax_const>\<open>_UNION\<close>),
     (\<^const_syntax>\<open>Inter\<close>, indexed_tr' \<^syntax_const>\<open>_INTER\<close>)]
  end
\<close>

definition power :: "i \<Rightarrow> i" (\<open>\<P>\<close>)
  where
    "\<P>(x) \<equiv> {y | y \<subseteq> x}"

lemma powerI [intro]: "Set(y) \<Longrightarrow> y \<subseteq> x \<Longrightarrow> y \<in> \<P>(x)"
  unfolding power_def by blast

lemma powerD [dest]: "y \<in> \<P>(x) \<Longrightarrow> y \<subseteq> x"
  unfolding power_def by blast

lemma power_iff [simp]: "y \<in> \<P>(x) \<longleftrightarrow> Set(y) \<and> y \<subseteq> x"
  by blast

definition succ :: "i \<Rightarrow> i" (\<open>S\<close>)
  where
    "S(x) \<equiv> x \<union> {x}"

lemma succI1 [intro]: "Set(x) \<Longrightarrow> x \<in> S(x)"
  unfolding succ_def by auto

lemma succI2 [intro]: "y \<in> x \<Longrightarrow> y \<in> S(x)"
  unfolding succ_def by auto

lemma succE [elim]: "y \<in> S(x) \<Longrightarrow> (y = x \<Longrightarrow> R) \<Longrightarrow> (y \<in> x \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding succ_def by auto

definition pair :: "[i, i] \<Rightarrow> i" (\<open>(\<open>notation=\<open>mixfix pair\<close>\<close>\<langle>_,_\<rangle>)\<close> 90)
  where
    "\<langle>a, b\<rangle> \<equiv> {{a}, {a, b}}"

lemma pairI1 [intro]: "Set({a}) \<Longrightarrow> {a} \<in> \<langle>a,b\<rangle>"
  unfolding pair_def by auto

lemma pairI2 [intro]: "Set({a,b}) \<Longrightarrow> {a, b} \<in> \<langle>a,b\<rangle>"
  unfolding pair_def by auto

lemma pairE: "x \<in> \<langle>a,b\<rangle> \<Longrightarrow> (x = {a} \<Longrightarrow> R) \<Longrightarrow> (x = {a, b} \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding pair_def by auto

definition fst :: "i \<Rightarrow> i"
  where
    "fst(A) = \<Union>{x | \<exists>Set(y). A = \<langle>x,y\<rangle>}"

definition snd :: "i \<Rightarrow> i"
  where
    "snd(A) = \<Union>{y | \<exists>Set(x). A = \<langle>x,y\<rangle>}"

section \<open>functions and relations\<close>

definition Pair :: "i \<Rightarrow> o"
  where
    "Pair(A) \<equiv> \<exists>Set(b c). A = \<langle>b,c\<rangle>"

lemma PairI [intro]:
  assumes "Set(a)" "Set(b)" "p = \<langle>a,b\<rangle>"
  shows "Pair(p)" using assms unfolding Pair_def by blast

lemma PairE [elim]: "Pair(p) \<Longrightarrow> (\<And>a b. Set(a) \<Longrightarrow> Set(b) \<Longrightarrow> p = \<langle>a,b\<rangle> \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Pair_def by blast

definition Rel :: "i \<Rightarrow> o"
  where
    "Rel(R) \<equiv> \<forall>p. p \<in> R \<longrightarrow> Pair(p)"

lemma RelI [intro]:
  assumes "\<And>p. p \<in> R \<Longrightarrow> Pair(p)"
  shows "Rel(R)"
  using assms unfolding Rel_def by auto

lemma RelE [elim]:
  assumes "Rel(R)" "p \<in> R"
  obtains x y where
    "Set(x)" "Set(y)" "p = \<langle>x,y\<rangle>"
  using assms unfolding Rel_def Pair_def by auto

definition Fun :: "i \<Rightarrow> o"
  where
    "Fun(F) \<equiv> Rel(F) \<and> (\<forall>Set(x y z). \<langle>x,y\<rangle> \<in> F \<and> \<langle>x,z\<rangle> \<in> F \<longrightarrow> y = z)"

lemma FunI [intro]:
  assumes "Rel(F)"
  and "\<And>x y z. \<lbrakk>Set(x); Set(y); Set(z); \<langle>x,y\<rangle> \<in> F; \<langle>x,z\<rangle> \<in> F\<rbrakk> \<Longrightarrow> y = z"
  shows "Fun(F)"
  using assms unfolding Fun_def by auto

lemma FunD1 [dest]: "Fun(F) \<Longrightarrow> Rel(F)"
  unfolding Fun_def by auto

lemma FunD2 [dest]:
  assumes "Fun(F)" "Set(x)" "Set(y)" "Set(z)"
  and "\<langle>x,y\<rangle> \<in> F" "\<langle>x,z\<rangle> \<in> F"
  shows "y = z"
  using assms unfolding Fun_def by auto

definition dom :: "i \<Rightarrow> i"
  where
    "dom(R) \<equiv> {x | \<exists>Set(y). \<langle>x,y\<rangle> \<in> R}"

lemma domI [intro]: "Set(x) \<Longrightarrow> Set(y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> x \<in> dom(R)"
  unfolding dom_def by auto

lemma domE [elim]: "x \<in> dom(R) \<Longrightarrow> (\<And>y. Set(y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> P) \<Longrightarrow> P"

  unfolding dom_def by blast

definition rng :: "i \<Rightarrow> i"
  where
    "rng(R) \<equiv> {y | \<exists>Set(x). \<langle>x,y\<rangle> \<in> R}"

lemma rngI [intro]: "Set(x) \<Longrightarrow> Set(y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> y \<in> rng(R)"
  unfolding rng_def by auto

lemma rngE [elim]: "y \<in> rng(R) \<Longrightarrow> (\<And>x. Set(x) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> P) \<Longrightarrow> P"

  unfolding rng_def by blast

definition ap :: "[i, i] \<Rightarrow> i" (infixr \<open>`\<close> 90)
  where
    "f`x \<equiv> \<Union>{y | \<langle>x,y\<rangle> \<in> f}"

axiomatization
where
  extensionality: "\<forall> C. C \<in> A \<longleftrightarrow> C \<in> B \<Longrightarrow> A = B"
and
  power_set: "Set(x) \<Longrightarrow> Set(\<P>(x))"
and
  pairing: "\<lbrakk>Set(x); Set(y)\<rbrakk> \<Longrightarrow> Set({x, y})"
and
  union: "Set(x) \<Longrightarrow> Set(\<Union>x)"
and
  foundation: "X \<noteq> {} \<Longrightarrow> \<exists>a \<in> X. \<forall>b \<in> X. b \<notin> a"
and
  infinity: "\<exists>Set(N). {} \<in> N \<and> (\<forall>n \<in> N. S(n) \<in> N)"
and
  replacement: "\<lbrakk>Fun(F); Set(dom(F))\<rbrakk> \<Longrightarrow> Set(rng(F))"
and
  global_choice: "Rel(R) \<Longrightarrow> \<exists>F. Fun(F) \<and> F \<subseteq> R \<and> dom(F) = dom(R)"

declare power_set [intro, simp] pairing [intro, simp] union [intro, simp]

lemma eqI [intro]:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "A = B"
  using assms by (blast intro: extensionality)

lemma subset_empty_iff [simp]: "A \<subseteq> {} \<longleftrightarrow> A = {}"
  by blast

lemma Rel_eqI:
  assumes "Rel(R)" "Rel(T)"
    and "\<And>x y. Set(x) \<Longrightarrow> Set(y) \<Longrightarrow>
      \<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<langle>x,y\<rangle> \<in> T"
  shows "R = T"
  by (rule eqI; use assms in blast)

lemma empty_set [intro, simp]: "Set({})"
  using infinity by blast

lemma singleton_set [intro, simp]:
  assumes "Set(x)"
  shows "Set({x})"
  using pairing[OF assms assms] by simp

lemma pair_set [intro, simp]:
  assumes "Set(x)" "Set(y)"
  shows "Set(\<langle>x,y\<rangle>)"
  using assms unfolding pair_def by simp

lemma singleton_inject:
  assumes "Set(a)"
  and "{a} = {b}"
  shows "a = b"
proof -
  have "a \<in> {a}" using assms(1) by simp
  then show ?thesis using assms(2) by auto
qed

definition If :: "[o, i, i] \<Rightarrow> i"
  ("if (_) then (_) else (_)" [10] 10)
  where
    "if P then a else b \<equiv> ({x \<in> a | P} \<union> {x \<in> b | \<not>P})"

lemma if_True [simp]:
  "P \<Longrightarrow> (if P then a else b) = a"
  unfolding If_def union_def comprehension by (rule eqI; auto)

lemma if_False [simp]:
  "\<not>P \<Longrightarrow> (if P then a else b) = b"
  unfolding If_def union_def comprehension by (rule eqI; auto)

lemma if_set [intro, simp]:
  assumes "Set(a)" "Set(b)"
  shows "Set(if P then a else b)"
  using assms by (cases P) simp_all

lemma if_mem_iff [simp]:
  "x \<in> (if P then A else B) \<longleftrightarrow> (P \<and> x \<in> A) \<or> (\<not>P \<and> x \<in> B)"
  by (cases P) simp_all

lemma pairing_same_set_eq_singleton [simp]:
  assumes "Set(x)"
  shows "{x, x} = {x}" by blast

lemma union_of_pair [simp]:
  assumes "Set(a)" "Set(b)"
  shows "\<Union>\<langle>a,b\<rangle> = {a, b}"
  by (rule eqI; use assms in \<open>auto simp: pair_def comprehension Bexist_def\<close>)

lemma pair_inject:
  assumes "Set(a)" "Set(b)" "Set(c)" "Set(d)"
      and "\<langle>a,b\<rangle> = \<langle>c,d\<rangle>"
  shows "a = c" "b = d" proof -
    from assms(1) have "Set({a})" by (rule singleton_set)
    hence "{a} \<in> \<langle>a,b\<rangle>" unfolding pair_def by auto
    with assms(5) have "{a} \<in> \<langle>c,d\<rangle>" by auto
    hence h: "{a} = {c} \<or> {a} = {c, d}" unfolding pair_def by (rule classAbsD)
    thus a_eq_c: "a = c" proof
      assume "{a} = {c}"
      with assms(1) show "a = c" by (rule singleton_inject)
    next
      assume "{a} = {c, d}"
      moreover from assms(3) have "c \<in> {c, d}" by auto
      ultimately have "c \<in> {a}" by auto
      hence "c = a" by auto
      thus "a = c" by auto
    qed
    from assms(5) have "\<Union>\<langle>a,b\<rangle> = \<Union>\<langle>c,d\<rangle>" by auto
    also from assms(1) assms(2) have "\<Union>\<langle>a,b\<rangle> = {a, b}" by simp
    also from assms(3) assms(4) have "\<Union>\<langle>c,d\<rangle> = {c, d}" by simp
    finally have ab_eq_cd: "{a, b} = {c, d}" .
    moreover from assms(2) have "b \<in> {a, b}" by auto
    ultimately have "b \<in> {c, d}" by auto
    hence "b = c \<or> b = d" ..
    thus "b = d" proof
      assume "b = d"
      thus "b = d" .
    next
      assume "b = c"
      with a_eq_c have "a = b" by simp
      hence "{a, b} = {b}" by simp
      with ab_eq_cd have "{c, d} = {b}" by simp
      moreover from assms(4) have "d \<in> {c, d}" by auto
      ultimately have "d \<in> {b}" by auto
      hence "d = b" ..
      thus "b = d" ..
    qed
  qed

lemma pair_iff [simp]:
  assumes "Set(a)" "Set(b)" "Set(c)" "Set(d)"
  shows "\<langle>a,b\<rangle> = \<langle>c,d\<rangle> \<longleftrightarrow> a = c \<and> b = d"
  using assms pair_inject by auto

lemma fst_pair [simp]:
  assumes "Set(a)" "Set(b)"
  shows "fst(\<langle>a,b\<rangle>) = a"
  by (rule eqI; use assms in \<open>auto simp: fst_def comprehension\<close>)

lemma snd_pair [simp]:
  assumes "Set(a)" "Set(b)"
  shows "snd(\<langle>a,b\<rangle>) = b"
  by (rule eqI; use assms in \<open>auto simp: snd_def comprehension\<close>)

definition Lambda :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where
    "Lambda(A, f) \<equiv> {\<langle>x,f(x)\<rangle> | x. x \<in> A}"

lemma LambdaI [intro]:
  assumes "x \<in> A" "Set(f(x))"
  shows "\<langle>x,f(x)\<rangle> \<in> Lambda(A, f)"
  using assms unfolding Lambda_def by blast

lemma LambdaE [elim]: "p \<in> Lambda(A, f) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> p = \<langle>x,f(x)\<rangle> \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Lambda_def by blast

lemma Lambda_pair_iff [simp]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))" "Set(a)" "Set(b)"
  shows "\<langle>a,b\<rangle> \<in> Lambda(A,f) \<longleftrightarrow> a \<in> A \<and> b = f(a)"
  using assms by (auto simp: Lambda_def comprehension)

text \<open>
  The lambda body must return sets throughout its domain: pair injectivity
  cannot identify arbitrary proper-class components. Keep this guard on the
  membership rule and on the derived domain, range, and application rules.
\<close>

text "Tagged union of a family of sets"

definition Sigma :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where
    "Sigma(I,F) \<equiv> \<Union>i\<in>I. \<Union>f\<in>F(i). {\<langle>i,f\<rangle>}"

text "function space"

definition Func :: "[i, i] \<Rightarrow> i" (infixr \<open>\<rightarrow>\<close> 60)
  where
    "Func(A,B) \<equiv> {f | Fun(f) \<and> dom(f) = A \<and> rng(f) \<subseteq> B}"

text "Product of a family of sets"

definition Pi :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where
    "Pi(I,F) \<equiv> {f \<in> I \<rightarrow> (\<Union>i \<in> I. F(i)) | \<forall>i \<in> I. f`i \<in> F(i)}"

syntax
  "_PROD" :: "[pttrn, i, i] \<Rightarrow> i" (\<open>(\<open>indent=3 notation=\<open>mixfix \<Prod>\<in>\<close>\<close>\<Prod>_\<in>_./ _)\<close> 10)
  "_SUM"  :: "[pttrn, i, i] \<Rightarrow> i" (\<open>(\<open>indent=3 notation=\<open>mixfix \<Sum>\<in>\<close>\<close>\<Sum>_\<in>_./ _)\<close> 10)
  "_lam"  :: "[pttrn, i, i] \<Rightarrow> i" (\<open>(\<open>indent=3 notation=\<open>mixfix \<lambda>\<in>\<close>\<close>\<lambda>_\<in>_./ _)\<close> 10)
syntax_consts
  "_PROD" \<rightleftharpoons> Pi and
  "_SUM" \<rightleftharpoons> Sigma and
  "_lam" \<rightleftharpoons> Lambda
translations
  "\<Prod>x\<in>A. B" \<rightleftharpoons> "CONST Pi(A, \<lambda>x. B)"
  "\<Sum>x\<in>A. B" \<rightleftharpoons> "CONST Sigma(A, \<lambda>x. B)"
  "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST Lambda(A, \<lambda>x. f)"


lemma Lambda_mem:
  assumes "x \<in> A"
      and "Set(f(x))"
  shows "\<langle>x,f(x)\<rangle> \<in> Lambda(A,f)"
  using assms by auto

lemma Lambda_rel [intro]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))"
  shows "Rel(Lambda(A,f))"
  by (rule RelI; use assms in \<open>auto elim!: LambdaE\<close>)

lemma Lambda_fun [intro]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))"
  shows "Fun(Lambda(A,f))"
  by (rule FunI; use assms in \<open>auto intro: Lambda_rel\<close>)

lemma Lambda_dom [simp]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))"
  shows "dom(Lambda(A,f)) = A"
  by (rule eqI; use assms in \<open>auto simp: dom_def comprehension\<close>)

lemma Lambda_ap [simp]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))" "a \<in> A"
  shows "Lambda(A,f)`a = f(a)"
  by (rule eqI; use assms in \<open>auto simp: ap_def comprehension\<close>)

lemma ap_eq:
  assumes "Fun(f)" "Set(x)" "Set(y)" "\<langle>x,y\<rangle> \<in> f"
  shows "f`x = y"
  by (rule eqI; use assms in \<open>auto simp: ap_def comprehension\<close>)

lemma ap_welldefined:
  assumes "Fun(f)" "Set(x)"
  and x_in_dom_f: "x \<in> dom(f)"
  shows "\<langle>x,f`x\<rangle> \<in> f" and "Set(f`x)"
proof -
  from x_in_dom_f obtain y where y: "Set(y)" "\<langle>x,y\<rangle> \<in> f" by auto
  have "f`x = y" using assms(1,2) y by (rule ap_eq)
  with y show "\<langle>x,f`x\<rangle> \<in> f" "Set(f`x)" by auto
qed

lemma ap_eqI:
  assumes "Fun(f)" "Set(x)" "Set(y)"
  and "\<langle>x,y\<rangle> \<in> f"
  shows "y = f`x" and "Set(f`x)"
  using assms ap_eq[OF assms] by auto

lemma ap_set [simp]: "Fun(f) \<Longrightarrow> x \<in> dom(f) \<Longrightarrow> Set(f`x)"
  by (blast intro: ap_welldefined(2))

text \<open>
  Keep application membership explicit. Registering it as a general introduction
  rule makes search try to construct functions for unrelated membership goals.
\<close>

lemma ap_mem: "Fun(f) \<Longrightarrow> x \<in> dom(f) \<Longrightarrow> \<langle>x,f`x\<rangle> \<in> f"
  by (blast intro: ap_welldefined(1))

lemma Fun_pair_iff [simp]:
  assumes "Fun(f)" "Set(x)" "Set(y)"
  shows "\<langle>x,y\<rangle> \<in> f \<longleftrightarrow> x \<in> dom(f) \<and> y = f`x"
  using assms by (auto intro: ap_mem dest: ap_eqI(1))

lemma Lambda_eta [simp]:
  assumes "Fun(f)"
  shows "Lambda(dom(f), \<lambda>x. f`x) = f"
  by (rule Rel_eqI; use assms in auto)

lemma Lambda_rng_iff [simp]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))"
  shows "y \<in> rng(Lambda(A,f)) \<longleftrightarrow> (\<exists>x \<in> A. y = f(x))"
  using assms by (auto simp: rng_def comprehension)

lemma separation [intro, simp]:
  assumes "Set(A)"
  shows "Set({x \<in> A | P(x)})"
proof -
  let ?f = "\<lambda>a \<in> A. if P(a) then {a} else {}"
  have "Fun(?f)" by (rule Lambda_fun) simp
  moreover have "Set(dom(?f))" using assms by simp
  ultimately have "Set(rng(?f))" by (rule replacement)
  then have "Set(\<Union>rng(?f))" by simp
  moreover have "\<Union>rng(?f) = {x \<in> A | P(x)}"
    by (rule eqI) (auto simp: Bexist_def)
  ultimately show ?thesis by simp
qed

lemma union_of_upair:
  assumes "Set(a)" "Set(b)"
  shows "\<Union>{a, b} = (a \<union> b)"
  using assms by blast

lemma union_set [intro, simp]:
  assumes "Set(a)" "Set(b)"
  shows "Set(a \<union> b)"
  using assms union[of "{a, b}"] by (simp add: union_of_upair)

lemma subclass_set:
  assumes "A \<subseteq> b" "Set(b)"
  shows "Set(A)" proof -
    let ?a = "{x \<in> b | x \<in> A}"
    from separation assms have "Set(?a)" by auto
    moreover from assms have "A = ?a" by blast
    ultimately show ?thesis by auto
  qed

lemma misc_simps [simp]:
  "{} \<union> A = A"
  "A \<union> {} = A"
  "\<bbbV> \<union> A = \<bbbV>"
  "A \<union> \<bbbV> = \<bbbV>"
  "{} \<inter> A = {}"
  "A \<inter> {} = {}"
  "\<bbbV> \<inter> A = A"
  "A \<inter> \<bbbV> = A"
  "{} \\ A = {}"
  "A \\ {} = A"
  "\<Union>{} = {}"
  "\<Inter>{} = \<bbbV>"
  by blast+

lemma simp_singleton [simp]:
  assumes "Set(a)"
  shows "\<Union>{a} = a" "\<Inter>{a} = a"
  using assms by blast+

lemma simp_pclass_singleton [simp]:
  assumes "PClass(a)"
  shows "{a} = {}"
  using assms by blast

lemma Lambda_cong:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f(x) = g(x)"
  and "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))"
  shows "Lambda(A,f) = Lambda(A,g)"
  by (rule eqI; use assms in \<open>auto elim!: LambdaE\<close>)

lemma funext:
  assumes fun: "Fun(f)" "Fun(g)"
  and "dom(f) = dom(g)"
  and "\<forall>x \<in> dom(f). f`x = g`x"
  shows "f = g"
proof -
  have "Lambda(dom(f), \<lambda>x. f`x) = Lambda(dom(f), \<lambda>x. g`x)"
    by (rule Lambda_cong; use assms in auto)
  also have "Lambda(dom(f), \<lambda>x. g`x) = g" using assms(3) fun(2) by simp
  finally show ?thesis using fun(1) by simp
qed

definition compose :: "[i, i] \<Rightarrow> i" (infixr \<open>\<circ>\<close> 60)
  where
    "P \<circ> R \<equiv> {\<langle>x,z\<rangle> | x y z. Set(x) \<and> Set(y) \<and> Set(z) \<and> \<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> P}"

lemma compose_rel [intro]: "Rel(P \<circ> R)"
  by (auto simp: compose_def Rel_def Pair_def comprehension)

lemma compose_pair_iff [simp]:
  assumes "Set(x)" "Set(z)"
  shows "\<langle>x,z\<rangle> \<in> P \<circ> R \<longleftrightarrow>
    (\<exists>Set(y). \<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> P)"
  using assms by (auto simp: compose_def comprehension cong: conj_cong)

definition restriction :: "[i, i] \<Rightarrow> i" (infixl \<open>\<restriction>\<close> 60)
  where
    "R \<restriction> A \<equiv> {\<langle>x,y\<rangle> | x y. Set(x) \<and> Set(y) \<and> \<langle>x,y\<rangle> \<in> R \<and> x \<in> A}"

definition inverse :: "i \<Rightarrow> i" ("(_\<inverse>)" [1000] 1000)
  where
    "R\<inverse> \<equiv> {\<langle>y,x\<rangle> | x y. Set(x) \<and> Set(y) \<and> \<langle>x,y\<rangle> \<in> R}"

lemma inverse_rel [intro]: "Rel(R\<inverse>)"
  by (auto simp: inverse_def Rel_def Pair_def comprehension)

lemma inverse_pair_iff [simp]:
  assumes "Set(x)" "Set(y)"
  shows "\<langle>x,y\<rangle> \<in> R\<inverse> \<longleftrightarrow> \<langle>y,x\<rangle> \<in> R"
  using assms by (auto simp: inverse_def comprehension)

definition fld :: "i \<Rightarrow> i"
  where
    "fld(R) \<equiv> dom(R) \<union> rng(R)"

definition image :: "[i, i] \<Rightarrow> i" (infixl \<open>``\<close> 90)
  where
    "F `` A \<equiv> {y | \<exists>x \<in> A. \<langle>x,y\<rangle> \<in> F}"

definition inverse_image :: "[i, i] \<Rightarrow> i" (infixl \<open>-``\<close> 90)
  where
    "F -`` A \<equiv> {x | \<exists>y \<in> A. \<langle>x,y\<rangle> \<in> F}"

lemma inv_involute:
  assumes "Rel(R)"
  shows "R\<inverse>\<inverse> = R"
  by (rule Rel_eqI; use assms in auto)

lemma compose_assoc: "P \<circ> (Q \<circ> R) = (P \<circ> Q) \<circ> R"
  by (rule Rel_eqI) (auto cong: conj_cong)

definition id :: "i"
  where
    "id \<equiv> \<lambda>x \<in> \<bbbV>. x"

lemma id_ap_x_eq_x:
  assumes "Set(x)"
  shows "id`x = x"
  using assms unfolding id_def by simp

definition Trans :: "i \<Rightarrow> o"
  where
    "Trans(A) \<equiv> \<forall>x \<in> A. x \<subseteq> A"

definition Ord :: "i \<Rightarrow> o"
  where
    "Ord(O) \<equiv> Set(O) \<and> Trans(O) \<and> (\<forall>o \<in> O. Trans(o))"

end
