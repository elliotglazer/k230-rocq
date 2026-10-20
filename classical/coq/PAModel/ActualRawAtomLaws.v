(** The raw quotient laws come from actual finite KLogic proofs. No law
    certificate, quotation equivalence, or axiom image is assumed here. *)
From RawLogic Require Import RawLogicCertificates.
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEquivalence RawLawTemplates RawLawInstances RawLawGraphs RawLawConsequences
  QuotientAtomTemplates QuotationPayloads SupportedQuotientEnvironments
  RawQuotientAtomCongruence.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma raw_parameter_atom_graph M equality k t x y z first second f :
  quotation_atom M equality
    (raw_parameters M k t x y z first) (raw_parameters M k t x y z second) t k f ->
  code_relation M (raw_parameters M k t x y z)
    (raw_atom_expression equality (CEvar 1) (CEvar first) (CEvar second) (CEvar 0)) f.
Proof.
  intro HA. apply (proj2 (raw_atom_expression_graph M (raw_parameters M k t x y z)
    equality (CEvar 1) (CEvar first) (CEvar second) (CEvar 0)
    t (raw_parameters M k t x y z first) (raw_parameters M k t x y z second) k f
    eq_refl eq_refl eq_refl eq_refl)). exact HA.
Qed.

Theorem actual_raw_quotient_atom_laws M t name marker :
  raw_empty_marker_graph M t name marker -> raw_quotient_atom_laws M t marker.
Proof.
  intros [HN [HTN HM]]. constructor.
  - intros x y k a b h [HK [HT [HX HY]]] HA HB HH.
    apply (raw_certificate_consequence RawSymmetry M k t x y x name marker h
      HK HT HX HY HX HN HTN HM).
    cbn [raw_consequence_expression].
    apply (raw_implication_expression_graph M (raw_parameters M k t x y x) _ _ a b h).
    + apply raw_parameter_atom_graph;exact HA.
    + apply raw_parameter_atom_graph;exact HB.
    + exact HH.
  - intros x y z k a b c [HK [HT [HX HY]]] [_ [_ [_ HZ]]] HA HB HC h HH.
    apply (raw_certificate_consequence RawTransitivity M k t x y z name marker h
      HK HT HX HY HZ HN HTN HM).
    cbn [raw_consequence_expression].
    apply (raw_binary_expression_graph M (raw_parameters M k t x y z) _ _ _ a b c h).
    + apply raw_parameter_atom_graph;exact HA.
    + apply raw_parameter_atom_graph;exact HB.
    + apply raw_parameter_atom_graph;exact HC.
    + exact HH.
  - intros x x' y k a b c [HK [HT [HX HX']]] [_ [_ [_ HY]]] HA HB HC h HH.
    apply (raw_certificate_consequence RawLeft M k t x x' y name marker h
      HK HT HX HX' HY HN HTN HM).
    cbn [raw_consequence_expression].
    apply (raw_binary_expression_graph M (raw_parameters M k t x x' y) _ _ _ a b c h).
    + apply raw_parameter_atom_graph;exact HA.
    + apply raw_parameter_atom_graph;exact HB.
    + apply raw_parameter_atom_graph;exact HC.
    + exact HH.
  - intros x y y' k a b c [HK [HT [HY HY']]] [_ [_ [HX _]]] HA HB HC h HH.
    apply (raw_certificate_consequence RawRight M k t x y y' name marker h
      HK HT HX HY HY' HN HTN HM).
    cbn [raw_consequence_expression].
    apply (raw_binary_expression_graph M (raw_parameters M k t x y y') _ _ _ a b c h).
    + apply raw_parameter_atom_graph;exact HA.
    + apply raw_parameter_atom_graph;exact HB.
    + apply raw_parameter_atom_graph;exact HC.
    + exact HH.
Qed.

Print Assumptions raw_parameter_atom_graph.
Print Assumptions actual_raw_quotient_atom_laws.
