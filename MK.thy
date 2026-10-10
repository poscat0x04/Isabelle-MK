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

lemma SetI [intro]: "x \<in> A \<Longrightarrow> Set(x)"
  unfolding Set_def by blast

lemma SetE [elim]: "Set(x) \<Longrightarrow> (\<And> A. x \<in> A \<Longrightarrow> R) \<Longrightarrow> R"
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

lemma classAbsE [elim]: 
  assumes "x \<in> {x | P(x)}"
  shows "Set(x)" "P(x)" proof
    from assms show "x \<in> {x | P(x)}" .
  next
    from comprehension have "x \<in> {x | P(x)} \<longleftrightarrow> Set(x) \<and> P(x)" .
    hence "x \<in> {x | P(x)} \<Longrightarrow> Set(x) \<and> P(x)" ..
    with assms have "Set(x) \<and> P(x)" by auto
    thus "P(x)" ..
  qed

syntax
  "_ClassAbsIn" :: "[pttrn, i, o] \<Rightarrow> i"
    ("(1{_ \<in> _ |/ _})")

syntax_consts
  "_ClassAbsIn" \<rightleftharpoons> ClassAbs

translations
  "{x \<in> A | P}" \<rightharpoonup> "{x | x \<in> A \<and> P}"

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

lemma BallI [intro]: "(\<And> x. x \<in> A \<Longrightarrow> P(x)) \<Longrightarrow> \<forall>x \<in> A. P(x)"
  unfolding Ball_def by blast

lemma BallE [elim]: "\<forall>x \<in> A. P(x) \<Longrightarrow> x \<in> A \<Longrightarrow> P(x)"
  unfolding Ball_def by blast

lemma BexistI [intro]: "x \<in> A \<Longrightarrow> P(x) \<Longrightarrow> \<exists>y \<in> A. P(y)"
  unfolding Bexist_def by blast

lemma BexistE [elim]: "\<exists>x \<in> A. P(x) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P(x) \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Bexist_def by blast

syntax
  "_Sall" :: "[idts, o] \<Rightarrow> o"
    (\<open>(\<open>indent=3 notation=\<open>binder \<forall>Set\<close>\<close>\<forall>Set'(_')./ _)\<close> 10)
  "_Sexist" :: "[idts, o] \<Rightarrow> o"
    (\<open>(\<open>indent=3 notation=\<open>binder \<exists>Set\<close>\<close>\<exists>Set'(_')./ _)\<close> 10)

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

lemma subsetI [intro]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  unfolding subset_def by blast

lemma subsetD [dest]: "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<in> B)"
  unfolding subset_def proof -
    assume "\<forall>x. x \<in> A \<longrightarrow> x \<in> B"
    thus "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B)" by blast
  qed

abbreviation empty :: "i" (\<open>\<emptyset>\<close>)
  where
    "\<emptyset> \<equiv> {x | False}"

notation (input) empty ("{}")

abbreviation universe :: "i" (\<open>\<bbbV>\<close>)
  where
    "\<bbbV> \<equiv> {x | True}"

definition inter :: "[i, i] \<Rightarrow> i" (infixl \<open>\<inter>\<close> 45)
  where
    "A \<inter> B \<equiv> {x | x \<in> A \<and> x \<in> B }"

lemma interI [intro]: "x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> (A \<inter> B)"
  unfolding inter_def by blast

lemma interE [elim]: "x \<in> (A \<inter> B) \<Longrightarrow> (x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding inter_def proof -
     assume "x \<in> {x | x \<in> A \<and> x \<in> B }"
     hence "x \<in> A \<and> x \<in> B" ..
     moreover assume "(x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> R)"
     ultimately show R by blast
  qed

definition union :: "[i, i] \<Rightarrow> i" (infixl \<open>\<union>\<close> 44)
  where
    "A \<union> B \<equiv> {x | x \<in> A \<or> x \<in> B }"

lemma unionI1 [intro]: "x \<in> A \<Longrightarrow> x \<in> (A \<union> B)"
  unfolding union_def by blast

lemma unionI2 [intro]: "x \<in> B \<Longrightarrow> x \<in> (A \<union> B)"
  unfolding union_def by blast

lemma unionE [elim]: "x \<in> (A \<union> B) \<Longrightarrow> (x \<in> A \<Longrightarrow> R) \<Longrightarrow> (x \<in> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding union_def proof -
    assume "x \<in> {x | x \<in> A \<or> x \<in> B}"
    hence "x \<in> A \<or> x \<in> B" ..
    moreover assume "x \<in> A \<Longrightarrow> R"
    moreover assume "x \<in> B \<Longrightarrow> R"
    ultimately show R by blast
  qed

definition diff :: "[i, i] \<Rightarrow> i" (infixl \<open>\\<close> 44)
  where
    "A \\ B \<equiv> {x | x \<in> A \<and> x \<notin> B}"

lemma diffI [intro]: "x \<in> A \<and> x \<notin> B \<Longrightarrow> x \<in> (A \\ B)"
  unfolding diff_def by blast

lemma diffE [elim]: "x \<in> (A \\ B) \<Longrightarrow> (x \<in> A \<Longrightarrow> x \<notin> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding diff_def proof -
    assume "x \<in> {x | x \<in> A \<and> x \<notin> B}"
    hence "x \<in> A \<and> x \<notin> B" ..
    moreover assume "(x \<in> A \<Longrightarrow> x \<notin> B \<Longrightarrow> R)"
    ultimately show R by blast
  qed

definition Inter :: "i \<Rightarrow> i" (\<open>(\<open>open_block notation=\<open>prefix \<Inter>\<close>\<close>\<Inter>_)\<close> [90] 90)
  where
    "\<Inter>A = {x | \<forall>a \<in> A. x \<in> a}"

lemma InterI [intro]: "Set(x) \<Longrightarrow> (\<And> a. a \<in> A \<Longrightarrow> x \<in> a) \<Longrightarrow> x \<in> \<Inter>A"
  unfolding Inter_def by blast

lemma InterE [elim]:"x \<in> \<Inter>A \<Longrightarrow> a \<in> A \<Longrightarrow> x \<in> a"
  unfolding Inter_def proof -
    assume "x \<in> {x | \<forall>a \<in> A. x \<in> a}"
    hence "\<forall>a \<in> A. x \<in> a" ..
    moreover assume "a \<in> A"
    ultimately show "x \<in> a" ..
  qed

definition Union :: "i \<Rightarrow> i" (\<open>(\<open>open_block notation=\<open>prefix \<Union>\<close>\<close>\<Union>_)\<close> [90] 90)
  where
    "\<Union>A = {x | \<exists>a \<in> A. x \<in> a}"

lemma UnionI [intro]: "x \<in> a \<and> a \<in> A \<Longrightarrow> x \<in> \<Union>A"
  unfolding Union_def by blast

lemma UnionE [elim]: "x \<in> \<Union>A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<in> a \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Union_def proof -
    assume "x \<in> {x | \<exists>a \<in> A. x \<in> a}"
    hence "\<exists>a \<in> A. x \<in> a" ..
    moreover assume "\<And>a. a \<in> A \<Longrightarrow> x \<in> a \<Longrightarrow> R"
    ultimately show R by (rule BexistE)
  qed

definition power :: "i \<Rightarrow> i" (\<open>\<P>\<close>)
  where
    "\<P>(x) \<equiv> {y | y \<subseteq> x}"

lemma powerI [intro]: "Set(y) \<Longrightarrow> y \<subseteq> x \<Longrightarrow> y \<in> \<P>(x)"
  unfolding power_def by blast

lemma powerE [elim]: "y \<in> \<P>(x) \<Longrightarrow> y \<subseteq> x"
  unfolding power_def proof -
    assume "y \<in> {y | y \<subseteq> x}"
    thus "y \<subseteq> x" ..
  qed

definition successor :: "i \<Rightarrow> i" (\<open>S\<close>)
  where
    "S(x) \<equiv> x \<union> {x}"

definition pair :: "[i, i] \<Rightarrow> i" (\<open>(\<open>notation=\<open>mixfix pair\<close>\<close> \<langle>_,_\<rangle>)\<close> 90)
  where
    "\<langle>a, b\<rangle> \<equiv> {{a}, {a, b}}"

definition fst :: "i \<Rightarrow> i"
  where
    "fst(A) = \<Union>{x | \<exists>Set(y). A = \<langle>x,y\<rangle>}"

definition snd :: "i \<Rightarrow> i"
  where
    "snd(A) = \<Union>{y | \<exists>Set(x). A = \<langle>x,y\<rangle>}"

section \<open>functions and relations\<close>

definition Pair :: "i \<Rightarrow> o"
  where
    "Pair(A) \<equiv> \<exists>Set(b c). A = \<langle>b, c\<rangle>"

definition Rel :: "i \<Rightarrow> o"
  where
    "Rel(R) \<equiv> \<forall>p. p \<in> R \<longrightarrow> Pair(p)"

definition Fun :: "i \<Rightarrow> o"
  where
    "Fun(F) \<equiv> Rel(F) \<and> (\<forall>Set(x y z). \<langle>x,y\<rangle> \<in> F \<and> \<langle>x,z\<rangle> \<in> F \<longrightarrow> y = z)"

definition dom :: "i \<Rightarrow> i"
  where
    "dom(R) \<equiv> {x | \<exists>Set(y). \<langle>x,y\<rangle> \<in> R}"

definition rng :: "i \<Rightarrow> i"
  where
    "rng(R) \<equiv> {y | \<exists>Set(x). \<langle>x,y\<rangle> \<in> R}"

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

lemma eqI [intro]:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "A = B" proof -
    from assms have "\<forall> C. C \<in> A \<longleftrightarrow> C \<in> B" ..
    with extensionality show ?thesis by auto
  qed

lemma pairing_same_set_eq_singleton [simp]:
  assumes "Set(x)"
  shows "{x, x} = {x}" proof
    fix y
    show "y \<in> {x, x} \<longleftrightarrow> y \<in> {x}" proof
      assume yx: "y \<in> {x}"
      hence "y = x" ..
      hence "y = x \<or> y = x" ..
      moreover from yx have "Set(y)" ..
      ultimately show "y \<in> {x, x}" by auto
    next
      assume yxx: "y \<in> {x, x}"
      hence "y = x \<or> y = x" ..
      hence "y = x" by blast
      moreover from yxx have "Set(y)" ..
      ultimately show "y \<in> {x}" by auto
    qed
  qed

lemma union_of_pair [simp]: 
  assumes "Set(a)" "Set(b)"
  shows "\<Union>\<langle>a,b\<rangle> = {a, b}" proof
    fix x
    show "x \<in> \<Union>\<langle>a,b\<rangle> \<longleftrightarrow> x \<in> {a, b}" proof
      assume "x \<in> \<Union>\<langle>a,b\<rangle>"
      then obtain y where h1: "y \<in> \<langle>a,b\<rangle>" and h2: "x \<in> y" ..
      from h1 have "y = {a} \<or> y = {a, b}" unfolding pair_def ..
      with h2 show "x \<in> {a, b}" by auto
    next
      assume h1: "x \<in> {a, b}"
      from assms have "Set({a, b})" by (rule pairing)
      hence "{a, b} \<in> \<langle>a,b\<rangle>" unfolding pair_def by auto
      with h1 show "x \<in> \<Union>\<langle>a,b\<rangle>" by auto
    qed
  qed

lemma singleton_set:
  assumes "Set(x)"
  shows "Set({x})" proof -
    from pairing assms have "Set({x, x})" by blast
    moreover have "{x, x} = {x}" by simp
    ultimately show ?thesis by auto
  qed

lemma singleton_inject [simp]:
  assumes "Set(a)"
  and "{a} = {b}"
  shows "a = b" proof -
    from assms(1) have "a \<in> {a}" by auto
    with assms(2) have "a \<in> {b}" by auto
    thus "a = b" by auto
  qed

lemma pair_inject:
  assumes "Set(a)" "Set(b)" "Set(c)" "Set(d)"
      and "\<langle>a,b\<rangle> = \<langle>c,d\<rangle>"
  shows "a = c \<and> b = d" proof -
    from assms(1) have "Set({a})" by (rule singleton_set)
    hence "{a} \<in> \<langle>a,b\<rangle>" unfolding pair_def by auto
    with assms(5) have "{a} \<in> \<langle>c,d\<rangle>" by auto
    hence h: "{a} = {c} \<or> {a} = {c, d}" unfolding pair_def by (rule classAbsE)
    hence a_eq_c: "a = c" proof
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
    hence "b = d" proof
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
    with a_eq_c show ?thesis by blast
  qed
end