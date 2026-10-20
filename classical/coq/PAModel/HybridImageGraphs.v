(** Quotient image predicates with independently chosen allocation bases for
    the input-membership atom and the source matrix. This allows later raw
    witnesses to be fresh in the context without constraining matrix depth. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NumericalEquivalence NumericalVacuitySteps NamedLeibnizSteps NamedSubstitution NamedBinderFresh NamedBinderConstructors FormulaFreshConstructors
  NamedExistential NumericalEnvironments NumericalQuotation QuotationPayloads QuotationHygiene
  SupportedQuotientEnvironments QuotationAtomRebase QuotationBinderFresh QuotationFormulaFresh TemplateBinderFresh TemplateFormulaFresh
  TemplateNamedSubstitution QuotationNamedSubstitution ReplacementMatrixQuotation SetFormulaCodes
  BinaryMatrixRenaming BinaryMatrixFresh BinaryMatrixRebase MatrixClauseRenaming RawCollectionRenaming.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition hybrid_image_graph M phi eb ec en t a y x atomBase matrixBase image :=
  exists q theta dom rest body,
    quotation_atom M false x a t atomBase q /\
    binary_matrix_quotation M phi eb ec en x y matrixBase t theta /\
    membership_graph M t x dom /\ quotation_binary M SFAnd q theta rest /\
    quotation_binary M SFAnd dom rest body /\ named_exists_graph M x body image.

Theorem hybrid_image_graph_total M phi eb ec en t a y x atomBase matrixBase :
  exists image,hybrid_image_graph M phi eb ec en t a y x atomBase matrixBase image.
Proof.
  destruct (quotation_atom_total M false x a t atomBase) as [q GQ].
  destruct (binary_matrix_total M phi eb ec en x y matrixBase t) as [theta GT].
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 1)) (t .: x .: fun _=>zeroM M)) as [dom GD].
  apply (proj1 (ns_atom_expression M _ false (CEvar 0) (CEvar 1) t x dom eq_refl eq_refl)) in GD.
  destruct (quotation_binary_total M SFAnd q theta) as [rest GR].
  destruct (quotation_binary_total M SFAnd dom rest) as [body GB].
  destruct (named_exists_graph_total M x body) as [image GI].
  exists image,q,theta,dom,rest,body;repeat split;assumption.
Qed.

Lemma numerical_named_exists_congruence M name a b ea eb :
  numerical_equivalent M a b -> named_exists_graph M name a ea -> named_exists_graph M name b eb ->
  numerical_equivalent M ea eb.
Proof.
  intros HE HA HB. set (rho:=name .: a .: b .: fun _=>zeroM M).
  apply (proj1 (numerical_equivalent_expression M rho
    (E_wex (CEvar 0) (CEvar 1)) (E_wex (CEvar 0) (CEvar 2)) ea eb
    (proj2 (named_exists_expression M rho (CEvar 0) (CEvar 1) name a ea eq_refl eq_refl) HA)
    (proj2 (named_exists_expression M rho (CEvar 0) (CEvar 2) name b eb eq_refl eq_refl) HB))).
  apply expression_equivalent_exists.
  exact (proj2 (numerical_equivalent_expression M rho (CEvar 1) (CEvar 2) a b eq_refl eq_refl) HE).
Qed.

Theorem hybrid_image_rebase M phi eb ec en t a y x ab0 mb0 ab1 mb1 image0 image1 :
  quotient_pair_safe M t x a ab0 -> quotient_pair_safe M t x a ab1 ->
  quotation_safe M eb ec en mb0 t -> quotation_safe M eb ec en mb1 t ->
  coding_lt M x mb0 -> coding_lt M y mb0 -> coding_lt M x mb1 -> coding_lt M y mb1 ->
  hybrid_image_graph M phi eb ec en t a y x ab0 mb0 image0 ->
  hybrid_image_graph M phi eb ec en t a y x ab1 mb1 image1 ->
  numerical_equivalent M image0 image1.
Proof.
  intros [HAB0 [HT0 [HX0 HA0]]] [HAB1 [HT1 [HX1 HA1]]] HM0 HM1 HXM0 HYM0 HXM1 HYM1
    [q0 [theta0 [dom0 [rest0 [body0 [GQ0 [GT0 [GD0 [GR0 [GB0 GI0]]]]]]]]]]
    [q1 [theta1 [dom1 [rest1 [body1 [GQ1 [GT1 [GD1 [GR1 [GB1 GI1]]]]]]]]]].
  assert (dom0=dom1).
  { apply (code_relation_functional M (E_wel (CEvar 0) (CEvar 1)) (t .: x .: fun _=>zeroM M)).
    - exact (proj2 (ns_atom_expression M _ false (CEvar 0) (CEvar 1) t x dom0 eq_refl eq_refl) GD0).
    - exact (proj2 (ns_atom_expression M _ false (CEvar 0) (CEvar 1) t x dom1 eq_refl eq_refl) GD1). }
  subst dom1. apply (numerical_named_exists_congruence M x body0 body1 image0 image1);try assumption.
  apply (numerical_equivalent_binary M SFAnd dom0 rest0 dom0 rest1 body0 body1);try assumption.
  - apply numerical_equivalent_refl.
  - apply (numerical_equivalent_binary M SFAnd q0 theta0 q1 theta1 rest0 rest1);try assumption.
    + exact (quotation_atom_rebase M false x a t ab0 ab1 q0 q1 HAB0 HAB1 HX0 HA0 HT0 HX1 HA1 HT1 GQ0 GQ1).
    + exact (binary_matrix_quotation_rebase M phi eb ec en x y mb0 mb1 t theta0 theta1
        HM0 HM1 HXM0 HYM0 HXM1 HYM1 GT0 GT1).
Qed.

Theorem hybrid_image_alpha M phi eb ec en t a y old new atomBase matrixBase image0 image1 :
  old<>zeroM M -> new<>zeroM M -> old<>new -> t<>old -> a<>old -> y<>old ->
  t<>new -> a<>new -> y<>new ->
  coding_lt M old atomBase -> coding_lt M new atomBase ->
  coding_lt M old matrixBase -> coding_lt M new matrixBase ->
  environment_avoids_name M eb ec en old -> environment_avoids_name M eb ec en new ->
  hybrid_image_graph M phi eb ec en t a y old atomBase matrixBase image0 ->
  hybrid_image_graph M phi eb ec en t a y new atomBase matrixBase image1 ->
  numerical_equivalent M image0 image1.
Proof.
  intros H0 H1 Hxy HT HA HY HTN HAN HYN HOa HNa HOm HNm EO EN
    [q0 [theta0 [dom0 [rest0 [body0 [GQ0 [GT0 [GD0 [GR0 [GB0 GI0]]]]]]]]]]
    [q1 [theta1 [dom1 [rest1 [body1 [GQ1 [GT1 [GD1 [GR1 [GB1 GI1]]]]]]]]]].
  apply (numerical_named_exists_alpha_equivalence_checked M body0 old new body1 image0 image1 H0 H1 Hxy).
  - apply (quotation_binary_binder_absent M SFAnd dom0 rest0 body0 old GB0).
    + exact (named_binder_absent_membership M t old dom0 old GD0).
    + apply (quotation_binary_binder_absent M SFAnd q0 theta0 rest0 old GR0).
      * exact (quotation_atom_binder_absent M false old a t atomBase q0 old GQ0 HOa).
      * exact (binary_matrix_binder_absent M phi eb ec en old y matrixBase t theta0 old GT0 HOm).
  - apply (quotation_binary_fresh M SFAnd dom0 rest0 body0 new GB0 H1).
    + apply (formula_fresh_membership_intro M t old dom0 new GD0 HTN Hxy).
    + apply (quotation_binary_fresh M SFAnd q0 theta0 rest0 new GR0 H1).
      * exact (quotation_atom_fresh M false old a t atomBase q0 new GQ0 HNa H1 Hxy HAN HTN).
      * exact (binary_matrix_formula_fresh M phi eb ec en old y matrixBase t theta0 new
          GT0 HNm H1 ltac:(congruence) Hxy HYN EN).
  - apply (quotation_binary_named_substitution M SFAnd dom0 rest0 dom1 rest1 body0 body1 old new H0);try assumption.
    + apply (ns_combine_atom M false t old dom0 t new dom1 old new GD0 GD1).
      * right;auto.
      * left;auto.
    + apply (quotation_binary_named_substitution M SFAnd q0 theta0 q1 theta1 rest0 rest1 old new H0);try assumption.
      * apply (quotation_atom_named_substitution M false old a new a t atomBase old new q0 q1 H0 HT HOa HNa);try assumption.
        -- left;auto.
        -- right;auto.
      * exact (binary_matrix_input_rename M phi eb ec en old new y matrixBase t theta0 theta1
          H0 HT HY HOm HNm EO GT0 GT1).
  - exact GI0.
  - exact GI1.
Qed.

Print Assumptions hybrid_image_graph_total.
Print Assumptions numerical_named_exists_congruence.
Print Assumptions hybrid_image_rebase.
Print Assumptions hybrid_image_alpha.




