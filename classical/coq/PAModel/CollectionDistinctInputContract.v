(** Complete the raw Collection boundary cases from its distinct-input
    family. The construction for distinct input remains an explicit premise. *)
From PAModel Require Import Model Arithmetic CodeExpressions NumericalProofs ProofTemplates
  NumericalEquivalence NamedLeibnizSteps NamedBinderFresh FreshNames TemplateFormulaFresh
  TemplateBinderFresh TemplateNamedSubstitution RawMarkerExclusions
  RawQuotientAtomCongruence RawCollectionProfile CollectionDegenerateInput.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition distinct_input_raw_collection_certificates M t marker :=
  forall a c u v theta,
    a<>t -> c<>zeroM M -> u<>zeroM M -> v<>zeroM M ->
    t<>c -> t<>u -> t<>v -> a<>c -> a<>u -> a<>v -> c<>u -> c<>v -> u<>v ->
    formula_fresh M theta c -> named_binder_absent M theta u -> named_binder_absent M theta v ->
    forall result, code_relation M (t .: a .: c .: u .: v .: theta .: fun _=>zeroM M)
      (E_raw_collection_statement (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) result ->
      numerical_implies M marker result.

Theorem raw_collection_certificates_from_distinct_input M t z marker :
  raw_empty_marker_graph M t z marker ->
  distinct_input_raw_collection_certificates M t marker ->
  raw_collection_template_certificates M t marker.
Proof.
  intros [HZ0 [HTZ HM]] HD a c u v theta HC0 HU0 HV0
    HTC HTU HTV HAC HAU HAV HCU HCV HUV HF HBU HBV out HOut.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H r=>axioms M ax r H) a t) as [E|HNe].
  - subst a.
    set (rho:=t .: t .: c .: u .: v .: theta .: z .: fun _=>zeroM M).
    set (Emp:=E_marker_empty (CEvar 0) (CEvar 6)).
    set (Target:=E_raw_collection_statement (CEvar 0) (CEvar 1)
      (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)).
    assert (HE:code_relation M rho Emp marker).
    { change (code_relation M rho (code_subst
        (fun idx=>match idx with 0=>CEvar 0|1=>CEvar 6|_=>CEconst 0 end)
        (E_wal (CEvar 1) (E_wn (E_wel (CEvar 1) (CEvar 0))))) marker).
      apply (proj2 (code_subst_graph M rho
        (fun idx=>match idx with 0=>CEvar 0|1=>CEvar 6|_=>CEconst 0 end)
        (t .: z .: fun _=>zeroM M) ltac:(intros [|[|idx]];reflexivity) _ marker)).
      exact HM. }
    assert (HO:code_relation M rho Target out).
    { change (code_relation M rho (code_subst
        (fun idx=>match idx with 0=>CEvar 0|1=>CEvar 1|2=>CEvar 2|3=>CEvar 3
          |4=>CEvar 4|5=>CEvar 5|_=>CEconst 0 end) Target) out).
      apply (proj2 (code_subst_graph M rho
        (fun idx=>match idx with 0=>CEvar 0|1=>CEvar 1|2=>CEvar 2|3=>CEvar 3
          |4=>CEvar 4|5=>CEvar 5|_=>CEconst 0 end)
        (t .: t .: c .: u .: v .: theta .: fun _=>zeroM M)
        ltac:(intros [|[|[|[|[|[|idx]]]]]];reflexivity) Target out)).
      exact HOut. }
    apply (proj1 (numerical_implies_expression M rho Emp Target marker out HE HO)).
    exact (numerical_raw_collection_degenerate_input M rho
      (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6)
      t z eq_refl eq_refl eq_refl (template_lt_different M _ _ HZ0)
      (template_lt_different M _ _ HTZ) (not_eq_sym (template_lt_different M _ _ HTZ))).
  - exact (HD a c u v theta HNe HC0 HU0 HV0 HTC HTU HTV HAC HAU HAV
      HCU HCV HUV HF HBU HBV out HOut).
Qed.

Print Assumptions raw_collection_certificates_from_distinct_input.
