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

lemma BallD [dest]: "\<forall>x \<in> A. P(x) \<Longrightarrow> x \<in> A \<Longrightarrow> P(x)"
  unfolding Ball_def by blast

lemma BexistI [intro]: "x \<in> A \<Longrightarrow> P(x) \<Longrightarrow> \<exists>y \<in> A. P(y)"
  unfolding Bexist_def by blast

lemma BexistE [elim]: "\<exists>x \<in> A. P(x) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P(x) \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Bexist_def by blast

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

definition inter :: "[i, i] \<Rightarrow> i" (infixl \<open>\<inter>\<close> 70)
  where
    "A \<inter> B \<equiv> {x | x \<in> A \<and> x \<in> B }"

lemma interI [intro]: "x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> (A \<inter> B)"
  unfolding inter_def by blast

lemma interE [elim]: "x \<in> (A \<inter> B) \<Longrightarrow> (x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding inter_def by blast

definition union :: "[i, i] \<Rightarrow> i" (infixl \<open>\<union>\<close> 65)
  where
    "A \<union> B \<equiv> {x | x \<in> A \<or> x \<in> B }"

lemma unionI1 [intro]: "x \<in> A \<Longrightarrow> x \<in> (A \<union> B)"
  unfolding union_def by blast

lemma unionI2 [intro]: "x \<in> B \<Longrightarrow> x \<in> (A \<union> B)"
  unfolding union_def by blast

lemma unionE [elim]: "x \<in> (A \<union> B) \<Longrightarrow> (x \<in> A \<Longrightarrow> R) \<Longrightarrow> (x \<in> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding union_def by blast

definition diff :: "[i, i] \<Rightarrow> i" (infixl \<open>\\<close> 65)
  where
    "A \\ B \<equiv> {x | x \<in> A \<and> x \<notin> B}"

lemma diffI [intro]: "x \<in> A \<and> x \<notin> B \<Longrightarrow> x \<in> (A \\ B)"
  unfolding diff_def by blast

lemma diffE [elim]: "x \<in> (A \\ B) \<Longrightarrow> (x \<in> A \<Longrightarrow> x \<notin> B \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding diff_def by blast

definition Inter :: "i \<Rightarrow> i" (\<open>(\<open>open_block notation=\<open>prefix \<Inter>\<close>\<close>\<Inter>_)\<close> [90] 90)
  where
    "\<Inter>A = {x | \<forall>a \<in> A. x \<in> a}"

lemma InterI [intro]: "Set(x) \<Longrightarrow> (\<And> a. a \<in> A \<Longrightarrow> x \<in> a) \<Longrightarrow> x \<in> \<Inter>A"
  unfolding Inter_def by blast

lemma InterD [dest]:"x \<in> \<Inter>A \<Longrightarrow> a \<in> A \<Longrightarrow> x \<in> a"
  unfolding Inter_def by blast

definition Union :: "i \<Rightarrow> i" (\<open>(\<open>open_block notation=\<open>prefix \<Union>\<close>\<close>\<Union>_)\<close> [90] 90)
  where
    "\<Union>A = {x | \<exists>a \<in> A. x \<in> a}"

lemma UnionI [intro]: "x \<in> a \<Longrightarrow> a \<in> A \<Longrightarrow> x \<in> \<Union>A"
  unfolding Union_def by blast

lemma UnionE [elim]: "x \<in> \<Union>A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<in> a \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Union_def by blast

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

definition successor :: "i \<Rightarrow> i" (\<open>S\<close>)
  where
    "S(x) \<equiv> x \<union> {x}"

definition pair :: "[i, i] \<Rightarrow> i" (\<open>(\<open>notation=\<open>mixfix pair\<close>\<close>\<langle>_,_\<rangle>)\<close> 90)
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
    "Pair(A) \<equiv> \<exists>Set(b c). A = \<langle>b,c\<rangle>"

lemma PairI [intro]:
  assumes "Set(a)" "Set(b)" "p = \<langle>a,b\<rangle>"
  shows "Pair(p)" unfolding Pair_def proof (intro exI conjI)
    from assms(1) show "Set(a)" .
  next
    from assms(2) show "Set(b)" .
  next
    from assms(3) show "p = \<langle>a,b\<rangle>" .
  qed

lemma PairE [elim]: "Pair(p) \<Longrightarrow> (\<And>a b. Set(a) \<Longrightarrow> Set(b) \<Longrightarrow> p = \<langle>a,b\<rangle> \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Pair_def proof -
    assume "\<exists>Set(b c). p = \<langle>b,c\<rangle>"
    then obtain x and y where "Set(x)" "Set(y)" "p = \<langle>x,y\<rangle>" by auto
    moreover assume "(\<And>a b. Set(a) \<Longrightarrow> Set(b) \<Longrightarrow> p = \<langle>a,b\<rangle> \<Longrightarrow> R)"
    ultimately show R by auto
  qed

definition Rel :: "i \<Rightarrow> o"
  where
    "Rel(R) \<equiv> \<forall>p. p \<in> R \<longrightarrow> Pair(p)"

lemma RelE:
  assumes "Rel(R)" "p \<in> R"
  obtains x y where
    "Set(x)" "Set(y)" "p = \<langle>x,y\<rangle>"
  using assms unfolding Rel_def Pair_def by auto

definition Fun :: "i \<Rightarrow> o"
  where
    "Fun(F) \<equiv> Rel(F) \<and> (\<forall>Set(x y z). \<langle>x,y\<rangle> \<in> F \<and> \<langle>x,z\<rangle> \<in> F \<longrightarrow> y = z)"

definition dom :: "i \<Rightarrow> i"
  where
    "dom(R) \<equiv> {x | \<exists>Set(y). \<langle>x,y\<rangle> \<in> R}"

lemma domI [intro]: "Set(x) \<Longrightarrow> Set(y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> x \<in> dom(R)"
  unfolding dom_def by auto

lemma domE [elim]: "x \<in> dom(R) \<Longrightarrow> (\<And>y. Set(y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> P) \<Longrightarrow> P"
  proof -
    assume "x \<in> dom(R)"
    hence "\<exists>Set(y). \<langle>x,y\<rangle> \<in> R" unfolding dom_def by auto
    then obtain y where "Set(y)" and "\<langle>x,y\<rangle> \<in> R" by auto
    moreover assume "\<And>y. Set(y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> P"
    ultimately show P by auto
  qed

definition rng :: "i \<Rightarrow> i"
  where
    "rng(R) \<equiv> {y | \<exists>Set(x). \<langle>x,y\<rangle> \<in> R}"

lemma rngI [intro]: "Set(x) \<Longrightarrow> Set(y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> y \<in> rng(R)"
  unfolding rng_def by auto

lemma rngE [elim]: "y \<in> rng(R) \<Longrightarrow> (\<And>x. Set(x) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> P) \<Longrightarrow> P"
  proof -
    assume "y \<in> rng(R)"
    hence "\<exists>Set(x). \<langle>x,y\<rangle> \<in> R" unfolding rng_def by auto
    then obtain x where "Set(x)" and "\<langle>x,y\<rangle> \<in> R" by auto
    moreover assume "\<And>x. Set(x) \<Longrightarrow> \<langle>x,y\<rangle> \<in> R \<Longrightarrow> P"
    ultimately show P by auto
  qed

definition ap :: "[i, i] \<Rightarrow> i" (infixl \<open>`\<close> 90)
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

lemma eqI [intro]:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "A = B" proof -
    from assms have "\<forall> C. C \<in> A \<longleftrightarrow> C \<in> B" ..
    with extensionality show ?thesis by auto
  qed

lemma empty_set: "Set({})"
  using infinity by blast

lemma singleton_set:
  assumes "Set(x)"
  shows "Set({x})" proof -
    from pairing assms have "Set({x, x})" by blast
    moreover have "{x, x} = {x}" by simp
    ultimately show ?thesis by auto
  qed

lemma pair_set:
  assumes "Set(x)" "Set(y)"
  shows "Set(\<langle>x,y\<rangle>)" unfolding pair_def proof -
    from assms(1) have "Set({x})" by (rule singleton_set)
    moreover from assms have "Set({x, y})" by (rule pairing)
    ultimately show "Set({{x}, {x, y}})" by (rule pairing)
  qed

lemma singleton_inject:
  assumes "Set(a)"
  and "{a} = {b}"
  shows "a = b" proof -
    from assms(1) have "a \<in> {a}" by auto
    with assms(2) have "a \<in> {b}" by auto
    thus "a = b" by auto
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

lemma if_set:
  assumes "Set(a)" "Set(b)"
  shows "Set(if P then a else b)" proof (cases P)
    case True
    hence "(if P then a else b) = a" by simp
    with assms show ?thesis by auto
  next
    case False
    hence "(if P then a else b) = b" by simp
    with assms show ?thesis by auto
  qed

lemma pairing_same_set_eq_singleton [simp]:
  assumes "Set(x)"
  shows "{x, x} = {x}" by blast

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

lemma pair_inject:
  assumes "Set(a)" "Set(b)" "Set(c)" "Set(d)"
      and "\<langle>a,b\<rangle> = \<langle>c,d\<rangle>"
  shows "a = c \<and> b = d" proof -
    from assms(1) have "Set({a})" by (rule singleton_set)
    hence "{a} \<in> \<langle>a,b\<rangle>" unfolding pair_def by auto
    with assms(5) have "{a} \<in> \<langle>c,d\<rangle>" by auto
    hence h: "{a} = {c} \<or> {a} = {c, d}" unfolding pair_def by (rule classAbsD)
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

lemma fst_pair [simp]:
  assumes "Set(a)" "Set(b)"
  shows "fst(\<langle>a,b\<rangle>) = a" proof
    fix z
    show "z \<in> fst(\<langle>a,b\<rangle>) \<longleftrightarrow> z \<in> a" unfolding fst_def proof
      assume "z \<in> \<Union>{x | \<exists>Set(y). \<langle>a,b\<rangle> = \<langle>x,y\<rangle>}"
      then obtain x where zx: "z \<in> x" and "x \<in> {x | \<exists>Set(y). \<langle>a,b\<rangle> = \<langle>x,y\<rangle>}" ..
      then have "\<exists>Set(y). \<langle>a,b\<rangle> = \<langle>x,y\<rangle>" and sx: "Set(x)" by auto
      then obtain y where "Set(y)" and "\<langle>a,b\<rangle>=\<langle>x,y\<rangle>" by auto
      with assms sx have "a = x \<and> b = y" by (rule pair_inject)
      hence "a = x" ..
      with zx show "z \<in> a" by auto
    next
      assume "z \<in> a"
      with assms show "z \<in> \<Union>{x | \<exists>Set(y). \<langle>a,b\<rangle> = \<langle>x,y\<rangle>}" by blast
    qed
  qed

lemma snd_pair [simp]:
  assumes "Set(a)" "Set(b)"
  shows "snd(\<langle>a,b\<rangle>) = b" proof
    fix z
    show "z \<in> snd(\<langle>a,b\<rangle>) \<longleftrightarrow> z \<in> b" unfolding snd_def proof
      assume "z \<in> \<Union>{y | \<exists>Set(x). \<langle>a,b\<rangle> = \<langle>x,y\<rangle>}"
      then obtain y where zy: "z \<in> y" and "y \<in> {y | \<exists>Set(x). \<langle>a,b\<rangle> = \<langle>x,y\<rangle>}" ..
      then have sy: "Set(y)" and "\<exists>Set(x). \<langle>a,b\<rangle> = \<langle>x,y\<rangle>" by auto
      then obtain x where sx: "Set(x)" and eq: "\<langle>a,b\<rangle> = \<langle>x,y\<rangle>" by auto
      from assms sx sy eq have "a = x \<and> b = y" by (rule pair_inject)
      hence "b = y" ..
      with zy show "z \<in> b" by auto
    next
      assume "z \<in> b"
      with assms show "z \<in> \<Union>{y | \<exists>Set(x). \<langle>a,b\<rangle> = \<langle>x,y\<rangle>}" by blast
    qed
  qed

definition Lambda :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where
    "Lambda(A, f) \<equiv> {\<langle>x,f(x)\<rangle> | x. x \<in> A}"

lemma LambdaI [intro]:
  assumes "x \<in> A" "Set(f(x))"
  shows "\<langle>x,f(x)\<rangle> \<in> Lambda(A, f)"
  unfolding Lambda_def proof
    from assms show "Set(\<langle>x,f(x)\<rangle>)" by (blast intro: pair_set)
  next
    from assms(1) show "\<exists>xa. xa \<in> A \<and> \<langle>x,f(x)\<rangle> = \<langle>xa,f(xa)\<rangle>" by blast
  qed

lemma LambdaE [elim]: "p \<in> Lambda(A, f) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> p = \<langle>x,f(x)\<rangle> \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Lambda_def proof -
    assume "p \<in> {\<langle>x,f(x)\<rangle> |x. x \<in> A}"
    hence "\<exists>x. x \<in> A \<and> p = \<langle>x,f(x)\<rangle>" ..
    then obtain "x" where "x \<in> A \<and> p = \<langle>x,f(x)\<rangle>" ..
    moreover assume "(\<And>x. x \<in> A \<Longrightarrow> p = \<langle>x,f(x)\<rangle> \<Longrightarrow> R)"
    ultimately show R by auto
  qed

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
  shows "\<langle>x,f(x)\<rangle> \<in> Lambda(A,f)" proof
    from assms(1) show "x \<in> A" .
  next
    from assms(2) show "Set(f(x))" .
  qed

lemma Lambda_rel:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))"
  shows "Rel(Lambda(A,f))" unfolding Rel_def proof (intro allI impI)
    fix p
    assume "p \<in> Lambda(A,f)"
    then obtain x where "x \<in> A" and p: "p = \<langle>x,f(x)\<rangle>" ..
    with assms have "Set(x)" "Set(f(x))" by auto
    with p show "Pair(p)" by auto
  qed

lemma Lambda_fun:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))"
  shows "Fun(Lambda(A,f))" unfolding Fun_def proof (intro conjI allI impI)
    from assms show "Rel(Lambda(A,f))" by (rule Lambda_rel)
  next
    fix x y z
    assume s: "Set(x)" "Set(y)" "Set(z)"
    assume "\<langle>x,y\<rangle> \<in> Lambda(A, f) \<and> \<langle>x,z\<rangle> \<in> Lambda(A,f)"
    hence xy: "\<langle>x,y\<rangle> \<in> Lambda(A,f)" and xz: "\<langle>x,z\<rangle> \<in> Lambda(A,f)" by auto

    from xy obtain x1 where "x1 \<in> A" and eq1: "\<langle>x,y\<rangle> = \<langle>x1,f(x1)\<rangle>" ..
    with assms have "Set(x1)" "Set(f(x1))" by auto
    with s eq1 pair_inject have "x = x1 \<and> y = f(x1)" by auto
    hence yeq: "y = f(x)" by auto

    from xz obtain x2 where "x2 \<in> A" and eq2: "\<langle>x,z\<rangle> = \<langle>x2,f(x2)\<rangle>" ..
    with assms have "Set(x2)" "Set(f(x2))" by auto
    with s eq2 pair_inject have "x = x2 \<and> z = f(x2)" by auto
    hence "z = f(x)" by auto
    with yeq show "y = z" by auto
  qed

lemma Lambda_dom [simp]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))"
  shows "dom(Lambda(A,f)) = A" unfolding dom_def proof (intro eqI iffI)
    fix x
    assume xa: "x \<in> A"
    moreover with assms have sfx: "Set(f(x))" by auto
    ultimately have "\<langle>x,f(x)\<rangle> \<in> Lambda(A,f)" by blast
    with sfx have "\<exists>Set(y). \<langle>x,y\<rangle> \<in> Lambda(A, f)" by auto
    moreover from xa have "Set(x)" ..
    ultimately show "x \<in> {x | \<exists>Set(y). \<langle>x,y\<rangle> \<in> Lambda(A, f)}" by auto
  next
    fix x
    assume "x \<in> {x | \<exists>Set(y). \<langle>x,y\<rangle> \<in> Lambda(A, f)}"
    hence "\<exists>Set(y). \<langle>x,y\<rangle> \<in> Lambda(A, f)" and sx: "Set(x)" by auto
    then obtain y where sy: "Set(y)" and "\<langle>x,y\<rangle> \<in> Lambda(A,f)" by auto
    then obtain x' where xa': "x' \<in> A" and eq: "\<langle>x,y\<rangle> = \<langle>x',f(x')\<rangle>" by auto
    with assms have "Set(x')" "Set(f(x'))" by auto
    with sx sy eq pair_inject have "x = x' \<and> y = f(x')" by auto
    with xa' show "x \<in> A" by auto
  qed

lemma Lambda_ap [simp]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> Set(f(x))" "a \<in> A"
  shows "Lambda(A,f)`a = f(a)" unfolding ap_def proof (intro eqI iffI)
    fix x
    assume "x \<in> \<Union>{y | \<langle>a,y\<rangle> \<in> Lambda(A, f)}"
    then obtain y where xy: "x \<in> y" and "y \<in> {y | \<langle>a,y\<rangle> \<in> Lambda(A,f)}" ..
    hence "Set(x)" and sy: "Set(y)" and "\<langle>a,y\<rangle> \<in> Lambda(A,f)" by auto
    then obtain a' where a'_in_A: "a' \<in> A" and eq: "\<langle>a,y\<rangle> = \<langle>a',f(a')\<rangle>" by auto
    hence sa': "Set(a')" by auto
    with assms a'_in_A have "Set(a)" and "Set(f(a'))" by auto
    with sy sa' eq pair_inject have "a = a'" and "y = f(a')" by auto
    hence "y = f(a)" by auto
    with xy show "x \<in> f(a)" by auto
  next
    fix x
    assume x_in_fa: "x \<in> f(a)"
    from assms have "Set(f(a))" by auto
    moreover with assms have "\<langle>a,f(a)\<rangle> \<in> Lambda(A,f)" by auto
    ultimately have "f(a) \<in> {y | \<langle>a,y\<rangle> \<in> Lambda(A,f)}" by auto
    with x_in_fa show "x \<in> \<Union>{y | \<langle>a,y\<rangle> \<in> Lambda(A, f)}" by auto
  qed

lemma ap_welldefined:
  assumes "Fun(f)" "Set(x)"
  and x_in_dom_f: "x \<in> dom(f)"
  shows "\<langle>x,f`x\<rangle> \<in> f" and "Set(f`x)" proof -
    from x_in_dom_f obtain y where sy: "Set(y)" and xy_in_f: "\<langle>x,y\<rangle> \<in> f" by auto
    moreover have f_ap_x: "f`x = y" unfolding ap_def proof (intro eqI iffI)
      fix a
      assume "a \<in> \<Union>{y | \<langle>x,y\<rangle> \<in> f}"
      then obtain b where "b \<in> {y | \<langle>x,y\<rangle> \<in> f}" and ab: "a \<in> b" by auto
      hence "\<langle>x,b\<rangle> \<in> f" and "Set(b)" by auto
      with assms(2) sy xy_in_f assms have "y = b" unfolding Fun_def by auto
      with ab show "a \<in> y" by auto
    next
      fix a
      assume "a \<in> y"
      with sy xy_in_f show "a \<in> \<Union>{y | \<langle>x,y\<rangle> \<in> f}" by blast
    qed
    ultimately show "\<langle>x,f`x\<rangle> \<in> f" by auto
    from f_ap_x sy show "Set(f`x)" by auto
  qed

lemma ap_eqI:
  assumes "Fun(f)" "Set(x)" "Set(y)"
  and "\<langle>x,y\<rangle> \<in> f"
  shows "y = f`x" and "Set(f`x)" proof -
    from assms have x_dom: "x \<in> dom(f)" unfolding dom_def by auto
    with assms ap_welldefined have "\<langle>x,f`x\<rangle> \<in> f" and "Set(f`x)" by auto
    with assms show "y = f`x" unfolding Fun_def by auto
    from assms x_dom ap_welldefined show "Set(f`x)" by auto
  qed

lemma Lambda_eta [simp]:
  assumes "Fun(f)"
  shows "Lambda(dom(f), \<lambda>x. f`x) = f" proof (intro eqI iffI)
    fix p
    assume "p \<in> (\<lambda>x\<in>dom(f). f ` x)"
    then obtain a where a_in_dom_f: "a \<in> dom(f)" and p_eq: "p = \<langle>a, f`a\<rangle>" by auto
    then obtain b where sb: "Set(b)" and ab_in_f: "\<langle>a,b\<rangle> \<in> f" by auto
    from a_in_dom_f have "Set(a)" ..
    with assms sb ab_in_f ap_eqI have "f`a = b" by auto
    with ab_in_f and p_eq show "p \<in> f" by auto
  next
    fix p
    assume pf: "p \<in> f"
    with assms have "\<exists>Set(x y). p = \<langle>x,y\<rangle>" unfolding Fun_def Rel_def Pair_def by auto
    then obtain x y where sxy: "Set(x)" "Set(y)" and p_eq: "p = \<langle>x,y\<rangle>" by auto
    with pf have xy_in_f: "\<langle>x,y\<rangle> \<in> f" by auto
    with sxy have x_in_domf: "x \<in> dom(f)" unfolding dom_def by auto
    from xy_in_f sxy assms ap_eqI have "y = f`x" "Set(f`x)" by auto
    with x_in_domf p_eq LambdaI show "p \<in> (\<lambda>x\<in>dom(f). f ` x)" by auto
  qed

lemma separation:
  assumes "Set(A)"
  shows "Set({x \<in> A | P(x)})" proof -
    let ?f = "\<lambda>a \<in> A. if P(a) then {a} else {}"
    have set_img: "\<And>a. a \<in> A \<Longrightarrow> Set(if P(a) then {a} else {})" proof -
      fix a
      assume "a \<in> A"
      with empty_set show "Set(if P(a) then {a} else {})"
        by (blast intro: singleton_set if_set)
    qed
    hence fun_f: "Fun(?f)" by (rule Lambda_fun)
    with set_img assms Lambda_dom have "Set(dom(?f))" by auto
    with fun_f have "Set(rng(?f))" by (rule replacement)
    hence range_union_set: "Set(\<Union>rng(?f))" by (rule union)
    have "\<Union>rng(?f) = {x \<in> A | P(x)}" proof
      fix x
      show "x \<in> \<Union>rng(?f) \<longleftrightarrow> x \<in> {x \<in> A | P(x)}" proof
        assume "x \<in> \<Union>rng(?f)"
        then obtain y where "y \<in> rng(?f)" and x_in_y: "x \<in> y" ..
        then obtain a where sa: "Set(a)" and sy: "Set(y)" and "\<langle>a,y\<rangle> \<in> ?f" by auto
        then obtain a' where a'_in_A: "a' \<in> A" and eq: "\<langle>a,y\<rangle> = \<langle>a', if P(a') then {a'} else {}\<rangle>" by auto
        hence sa': "Set(a')" by auto
        with empty_set if_set singleton_set have "Set(if P(a') then {a'} else {})" by auto
        with sa sy sa' eq pair_inject have a_eq_a': "a = a'" and yeq: "y = (if P(a') then {a'} else {})" by auto
        show "x \<in> {x \<in> A | P(x)}" proof (cases "P(a')")
          case True
          with yeq if_True have "y = {a'}" by auto
          with x_in_y have "x = a'" by auto
          with a'_in_A True have "x \<in> A" and "P(x)" by auto
          thus ?thesis by auto
        next
          case False
          with yeq if_False have "y = {}" by auto
          with x_in_y have False by auto
          thus ?thesis by auto
        qed
      next
        assume "x \<in> {x \<in> A | P(x)}"
        hence "x \<in> A \<and> P(x)" ..
        hence sx: "Set(x)" and xa: "x \<in> A" and px: "P(x)" by auto
        with singleton_set have ssx: "Set({x})" by auto
        with empty_set if_set have "Set(if P(x) then {x} else {})" by auto
        with xa have "\<langle>x,if P(x) then {x} else {}\<rangle> \<in> ?f" by auto
        moreover from px if_True have "(if P(x) then {x} else {}) = {x}" by auto
        ultimately have "\<langle>x,{x}\<rangle> \<in> ?f" by auto
        with sx ssx have "{x} \<in> rng(?f)" by auto
        moreover from sx have "x \<in> {x}" by auto
        ultimately show "x \<in> \<Union>rng(?f)" by auto
      qed
    qed
    with range_union_set show ?thesis by simp
  qed

lemma union_of_upair:
  assumes "Set(a)" "Set(b)"
  shows "\<Union>{a, b} = (a \<union> b)" proof (intro eqI iffI)
    fix x
    assume "x \<in> \<Union>{a, b}"
    then obtain y where xy: "x \<in> y" and y: "y \<in> {a, b}" by auto
    from y have "y = a \<or> y = b" by blast
    with xy show "x \<in> (a \<union> b)" by blast
  next
    fix x
    assume "x \<in> (a \<union> b)"
    hence "x \<in> a \<or> x \<in> b" by auto
    with assms show "x \<in> \<Union>{a, b}" by blast
  qed

lemma union_set:
  assumes "Set(a)" "Set(b)"
  shows "Set(a \<union> b)" proof -
    from assms have "Set({a, b})" by (rule pairing)
    hence "Set(\<Union>{a, b})" by (rule union)
    moreover with assms union_of_upair have "\<Union>{a, b} = (a \<union> b)" by auto
    ultimately show ?thesis by auto
  qed

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
  "{} \<inter> A = {}"
  "A \<inter> {} = {}"
  "{} \\ A = {}"
  "A \\ {} = A"
  "\<Union>{} = {}"
  "\<Inter>{} = \<bbbV>"
  by blast+

lemma simp_singleton [simp]:
  assumes "Set(a)"
  shows "\<Union>{a} = a" "\<Inter>{a} = a"
  using assms by blast+

end
