(** An actual binary matrix supplies an arbitrary output witness to a
    raw existential. The output binder is fresh above the witness and input. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent QuotientAtomTemplates
  NamedSubstitution NamedLeibnizSteps TemplateNamedSubstitution NamedBinderFresh NamedBinderConstructors NumericalEnvironments
  QuotationHygiene QuotationPayloads SetFormulaCodes QuotationNamedSubstitution QuotationBinderFresh
  QuotedInstantiationRules ContextualProofs ContextualGuardedQuantifiers
  ReplacementMatrixQuotation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem binary_matrix_output_named_substitution M phi eb ec en u z y t thetaZ thetaY :
  quotation_safe M eb ec en z t -> coding_lt M u z -> coding_lt M y z ->
  binary_matrix_quotation M phi eb ec en u z (succM M z) t thetaZ ->
  binary_matrix_quotation M phi eb ec en u y (succM M z) t thetaY ->
  named_substitution M thetaZ z y thetaY.
Proof.
  intros HS HU HY
    [zb [zc [zn [ub [uc [un [HZ [HUZ HThetaZ]]]]]]]]
    [yb [yc [yn [vb [vc [vn [HYenv [HUY HThetaY]]]]]]]].
  apply (numerical_quotation_head_replacement M phi ub uc un vb vc vn z t y
    thetaZ thetaY (proj1 HS) HY);[|exact HThetaZ|exact HThetaY].
  apply (environment_named_replace_cons M zb zc zn yb yc yn ub uc un vb vc vn z y u).
  - exact (environment_cons_head_replacement M eb ec en zb zc zn yb yc yn z y
      (proj2 HS) HZ HYenv).
  - intro E. exact (template_lt_different M u z HU (eq_sym E)).
  - exact HUZ.
  - exact HUY.
Qed.

Theorem contextual_binary_matrix_output_exists M phi eb ec en cb cc cn u z y t
    thetaZ thetaY domY ex :
  quotation_safe M eb ec en z t -> coding_lt M u z -> coding_lt M y z ->
  binary_matrix_quotation M phi eb ec en u z (succM M z) t thetaZ ->
  binary_matrix_quotation M phi eb ec en u y (succM M z) t thetaY ->
  membership_graph M t y domY -> quotation_quantifier M false z t thetaZ ex ->
  contextually_provable M cb cc cn domY -> contextually_provable M cb cc cn thetaY ->
  contextually_provable M cb cc cn ex.
Proof.
  intros HS HU HY HThetaZ HThetaY HDY HEx PDY PThetaY.
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 1))
    (t .: z .: fun _=>zeroM M)) as [domZ HDZ].
  assert (GDZ : membership_graph M t z domZ).
  { exact (proj1 (ns_atom_expression M (t .: z .: fun _=>zeroM M) false
      (CEvar 0) (CEvar 1) t z domZ eq_refl eq_refl) HDZ). }
  destruct (quotation_binary_total M SFAnd domZ thetaZ) as [conjZ HCZ].
  destruct (quotation_binary_total M SFAnd domY thetaY) as [conjY HCY].
  assert (HZY : z<>y) by exact (template_lt_different M y z HY).
  assert (HZ0 : z<>zeroM M).
  { intro E;subst z;exact (coding_not_lt_zero M y HY). }
  assert (HSub : named_substitution M thetaZ z y thetaY).
  { exact (binary_matrix_output_named_substitution M phi eb ec en u z y t thetaZ thetaY
      HS HU HY HThetaZ HThetaY). }
  destruct HThetaZ as [zb [zc [zn [ub [uc [un [HZ [HUZ HThetaZ]]]]]]]].
  apply (contextual_guarded_exists_intro M cb cc cn z y t thetaZ thetaY
    domZ domY conjZ conjY ex HZY GDZ HDY HCZ HCY).
  - apply (quotation_binary_binder_absent M SFAnd domZ thetaZ conjZ z HCZ).
    + exact (named_binder_absent_membership M t z domZ z GDZ).
    + exact (numerical_quotation_matrix_binder_absent M phi ub uc un z t thetaZ HThetaZ).
  - apply (quotation_binary_binder_absent M SFAnd domZ thetaZ conjZ y HCZ).
    + exact (named_binder_absent_membership M t z domZ y GDZ).
    + exact (numerical_quotation_binder_fresh M phi ub uc un (succM M z) t thetaZ y
        HThetaZ (coding_lt_trans M y z (succM M z) HY (coding_lt_succ M z))).
  - exact (quotation_binary_named_substitution M SFAnd domZ thetaZ domY thetaY conjZ conjY z y
      HZ0 (quoted_domain_named_substitution M t z y domZ domY (proj1 HS) GDZ HDY) HSub HCZ HCY).
  - exact HEx.
  - exact PDY.
  - exact PThetaY.
Qed.

Print Assumptions binary_matrix_output_named_substitution.
Print Assumptions contextual_binary_matrix_output_exists.
