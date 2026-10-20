(** The three-bound-variable instance of container identification, and
    the literal matrix map of canonical CB monotonicity. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation RenamingSubstitution
  SourceOrdinalInitialMonoMaps SourceOrdinalMonotoneMaps SourceSubstitutionComposition SchemaRenamingDescriptors SubstitutionSource.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_cb_collapse_three M rb rc rn:=exists b c ab ac an tb tc tn,
  substitution_lookup M b c(code_numeral M 1)(zeroM M)(zeroM M)(zeroM M) /\
  substitution_lift M b c(code_numeral M 1)(zeroM M)ab ac an /\
  substitution_lift M ab ac an(code_numeral M 1)tb tc tn /\
  substitution_lift M tb tc tn(code_numeral M 2)rb rc rn.

Theorem source_cb_collapse_three_total M:exists rb rc rn,source_cb_collapse_three M rb rc rn.
Proof.
  destruct(substitution_singleton_total M(zeroM M)) as(b&c&HHead&HTail).
  destruct(substitution_lift_total M b c(code_numeral M 1)(zeroM M)) as(ab&ac&an&H1).
  destruct(substitution_lift_total M ab ac an(code_numeral M 1)) as(tb&tc&tn&H2).
  destruct(substitution_lift_total M tb tc tn(code_numeral M 2)) as(rb&rc&rn&H3).
  exists rb,rc,rn,b,c,ab,ac,an,tb,tc,tn. auto.
Qed.

Theorem source_cb_collapse_three_head M rb rc rn i:
  source_cb_collapse_three M rb rc rn ->(i<3)%nat ->
  substitution_lookup M rb rc rn(code_numeral M 3)(code_numeral M i)(code_numeral M i).
Proof.
  intros(b&c&ab&ac&an&tb&tc&tn&H0&H1&H2&H3)HI.
  destruct i as[|[|[|i]]];try lia.
  - exact(proj1(proj2 H3)).
  - exact(proj2(proj2 H3)(zeroM M)(zeroM M)(proj1(proj2 H2))).
  - exact(proj2(proj2 H3)(code_numeral M 1)(code_numeral M 1)
      (proj2(proj2 H2)(zeroM M)(zeroM M)(proj1(proj2 H1)))).
Qed.

Theorem source_cb_collapse_three_tail M rb rc rn i:
  source_cb_collapse_three M rb rc rn ->
  substitution_lookup M rb rc rn(code_numeral M 3)
    (succM M(succM M(succM M(succM M i))))(succM M(succM M(succM M i))).
Proof.
  intros(b&c&ab&ac&an&tb&tc&tn&H0&H1&H2&H3).
  apply(proj2(proj2 H3)(succM M(succM M(succM M i)))(succM M(succM M i))).
  apply(proj2(proj2 H2)(succM M(succM M i))(succM M i)).
  apply(proj2(proj2 H1)(succM M i)i). apply substitution_singleton_tail.
Qed.

Definition source_cb_mono_matrix M right phi row :=numerical_renaming M phi
  (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 1)row.

Lemma source_cb_mono_first M right:renaming_lookup M
  (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 1)
  (zeroM M)(code_numeral M(source_oc_mono_first right)).
Proof.
  apply(proj2(renaming_lookup_inside M _ _ _ _ _ _(coding_zero_lt_succ M(code_numeral M 1)))).
  exact(proj1(renaming_lookup_inside M _ _ _ _ _ _(coding_zero_lt_succ M(code_numeral M 1)))
    (source_oc_mono_first_lookup M right)).
Qed.
Lemma source_cb_mono_second M right:renaming_lookup M
  (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 1)
  (code_numeral M 1)(code_numeral M 2).
Proof.
  apply(proj2(renaming_lookup_inside M _ _ _ _ _ _(coding_lt_succ M(code_numeral M 1)))).
  exact(proj1(renaming_lookup_inside M _ _ _ _ _ _(coding_lt_succ M(code_numeral M 1)))
    (source_oc_mono_second_lookup M right)).
Qed.
Lemma source_cb_mono_tail M right i:renaming_lookup M
  (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 1)
  (succM M(succM M i))(succM M(succM M(succM M i))).
Proof.
  apply(proj2(renaming_lookup_outside M _ _ _ _ _ _ ltac:(intro H;
    exact(coding_not_lt_zero M i(proj1(coding_lt_succ_cancel M i(zeroM M))
      (proj1(coding_lt_succ_cancel M(succM M i)(code_numeral M 1))H)))))).
  change(succM M(succM M(succM M i))=addM M(succM M(succM M i))(code_numeral M 1)).
  cbn[code_numeral]. now rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_cb_initial_mono_matrix_collapse M right phi old rb rc rn out k:
  source_bounded M phi k ->source_oc_initial_mono_matrix M right phi old ->
  source_cb_collapse_three M rb rc rn ->numerical_substitution M old rb rc rn(code_numeral M 3)out ->
  source_cb_mono_matrix M right phi out.
Proof.
  intros HB HR HM HS.
  pose proof(proj1(numerical_renaming_substitution M phi _ _ _(code_numeral M 2)old)HR) as HOld.
  rewrite descriptor_numeral_add in HOld.
  apply(proj2(numerical_renaming_substitution M phi _ _ _(code_numeral M 1)out)).
  rewrite descriptor_numeral_add.
  apply(numerical_substitution_composition M phi k
    (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 4)
    rb rc rn(code_numeral M 3)
    (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 3)
    old out HB HOld HS).
  intros i j v HI HFirst HSecond.
  assert(HFirst':renaming_lookup M(code_numeral M(source_oc_mono_dividend right))
    (code_numeral M 3)(code_numeral M 2)(code_numeral M 2)i j).
  { apply(proj2(renaming_substitution_lookup M _ _ _ _ i j)). now rewrite descriptor_numeral_add. }
  pose proof(renaming_substitution_lookup M(code_numeral M(source_oc_mono_dividend right))
    (code_numeral M 3)(code_numeral M 2)(code_numeral M 1)i v) as HConvert.
  rewrite descriptor_numeral_add in HConvert. apply(proj1 HConvert).
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[E|[idx E]];subst i.
  - pose proof(renaming_lookup_functional M _ _ _ _ _ j _(HFirst')(source_oc_initial_mono_first M right)) as E.
    subst j. assert(HFix:substitution_lookup M rb rc rn(code_numeral M 3)
      (code_numeral M(source_oc_mono_first right))(code_numeral M(source_oc_mono_first right))).
    { destruct right;cbn[source_oc_mono_first];
        apply(source_cb_collapse_three_head M rb rc rn _ HM);lia. }
    pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HSecond HFix) as E.
    subst v. exact(source_cb_mono_first M right).
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)idx)
      as[E|[tail E]];subst idx.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HFirst'(source_oc_initial_mono_second M right)) as E.
      subst j. pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HSecond
        (source_cb_collapse_three_head M rb rc rn 2 HM ltac:(lia))) as E.
      subst v. exact(source_cb_mono_second M right).
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HFirst'(source_oc_initial_mono_tail M right tail)) as E.
      subst j. pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HSecond
        (source_cb_collapse_three_tail M rb rc rn tail HM)) as E.
      subst v. exact(source_cb_mono_tail M right tail).
Qed.

Print Assumptions source_cb_collapse_three_total.
Print Assumptions source_cb_collapse_three_head.
Print Assumptions source_cb_collapse_three_tail.
Print Assumptions source_cb_initial_mono_matrix_collapse.
