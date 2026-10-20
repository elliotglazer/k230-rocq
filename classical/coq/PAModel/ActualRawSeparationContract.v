(** Exact raw-domain Separation contract used by the source-schema transfer.
    The empty-marker binder is first moved above all parameter names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  ProofTemplates NumericalProofs NumericalEquivalence NamedLeibnizSteps
  NamedBinderFresh FreshNames FixedSourceBounds BootstrapSpecializations
  SeparationAllocation RawSeparationContract RawMarkerExclusions EmptyRebind QuotationFixedSource
  NumericalRawDomainSeparation RawSeparationNormalizedEnvelope
  QuotedSameContainer RawSchemaCoreComparison.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem actual_raw_domain_separation_certificates M marker :
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  raw_domain_separation_certificates M marker.
Proof.
  intros HMarker a w theta H1a Hbasew HF_a HF_c HBind out HOut.
  set (c:=succM M a).
  destruct (separation_named_bounds M a H1a) as [H0a [Hac [Hcc [Hlast H2c]]]].
  assert (Hcw:coding_lt M c w).
  { exact (coding_lt_trans M c (separation_base M a) w
      (coding_lt_trans M c (succM M c) (separation_base M a) Hcc Hlast) Hbasew). }
  assert (Haw:coding_lt M a w) by exact (coding_lt_trans M a c w Hac Hcw).
  assert (H1w:coding_lt M (code_numeral M 1) w) by exact (coding_lt_trans M _ a w H1a Haw).
  assert (H2w:coding_lt M (code_numeral M 2) w) by exact (coding_lt_trans M _ c w H2c Hcw).
  assert (H0c:coding_lt M (zeroM M) c) by exact (coding_lt_trans M _ a c H0a Hac).
  assert (H0w:coding_lt M (zeroM M) w) by exact (coding_lt_trans M _ a w H0a Haw).
  set (z:=separation_witness_name M w marker theta).
  destruct (separation_witness_bounds M w marker theta) as [HBz [HMz HThetaZ]].
  assert (Hwbase:coding_lt M w (separation_base M w)).
  { unfold separation_base. eapply coding_lt_trans;[apply coding_lt_succ|].
    eapply coding_lt_trans;apply coding_lt_succ. }
  assert (Hwz:coding_lt M w z) by exact (coding_lt_trans M w _ z Hwbase HBz).
  assert (Haz:coding_lt M a z) by exact (coding_lt_trans M a w z Haw Hwz).
  assert (H1z:coding_lt M (code_numeral M 1) z) by exact (coding_lt_trans M _ w z H1w Hwz).
  assert (H2z:coding_lt M (code_numeral M 2) z) by exact (coding_lt_trans M _ w z H2w Hwz).
  assert (H0z:coding_lt M (zeroM M) z) by exact (coding_lt_trans M _ w z H0w Hwz).
  assert (D:forall i j,i<4 -> j<4 -> i<>j ->
      raw_domain_roles M w a (code_numeral M 1) z i <>
      raw_domain_roles M w a (code_numeral M 1) z j).
  { intros i j Hi Hj Hij.
    pose proof (separation_lt_neq M a w Haw).
    pose proof (separation_lt_neq M (code_numeral M 1) w H1w).
    pose proof (separation_lt_neq M w z Hwz).
    pose proof (separation_lt_neq M (code_numeral M 1) a H1a).
    pose proof (separation_lt_neq M a z Haz).
    pose proof (separation_lt_neq M (code_numeral M 1) z H1z).
    destruct i as [|[|[|[|i]]]];destruct j as [|[|[|[|j]]]];
      cbn [raw_domain_roles] in *;try lia;congruence. }
  assert (N:forall i,i<4 -> raw_domain_roles M w a (code_numeral M 1) z i<>zeroM M).
  { intros i Hi.
    pose proof (separation_lt_neq M (zeroM M) w H0w).
    pose proof (separation_lt_neq M (zeroM M) a H0a).
    pose proof (separation_lt_neq M (zeroM M) z H0z).
    pose proof (separation_lt_neq M (zeroM M) (code_numeral M 1) (coding_lt_succ M _)).
    destruct i as [|[|[|[|i]]]];cbn [raw_domain_roles] in *;try lia;congruence. }
  assert (HT: named_binder_absent M theta (code_numeral M 1)).
  { apply HBind. exact (coding_lt_trans M _ w (succM M w) H1w (coding_lt_succ M w)). }
  pose proof (numerical_raw_domain_separation M w a (code_numeral M 1) z theta c D N HT
    (not_eq_sym (separation_lt_neq M (zeroM M) c H0c))
    (separation_lt_neq M _ c (coding_lt_trans M _ a c H1a Hac))
    (separation_lt_neq M a c Hac) (not_eq_sym (separation_lt_neq M c w Hcw)) HF_c) as HGeneric.
  set (rho:=a .: w .: theta .: z .: fun _=>zeroM M).
  set (Emp:=E_marker_empty (CEconst 1) (CEvar 3)).
  set (Target:=E_raw_domain_separation (CEvar 0) (CEvar 1) (CEvar 2)).
  assert (HInstance:ns_proof M rho (E_wim Emp Target)).
  { intros f Hf.
    set (sigma:=fun idx=>match idx with
      |0=>CEvar 1|1=>CEvar 0|3=>CEconst 1|5=>CEvar 3|6=>CEvar 2
      |7=>CEadd (CEvar 0) (CEconst 1)|_=>CEconst 0 end).
    change (code_relation M rho (code_subst sigma E_raw_domain_statement) f) in Hf.
    assert (HSigma:forall idx,code_relation M rho (sigma idx)
      (raw_domain_environment M w a (code_numeral M 1) z theta c idx)).
    { intros idx. destruct idx as [|[|[|[|[|[|[|[|idx]]]]]]]];try reflexivity.
      change (code_relation M rho (CEadd (CEvar 0) (CEconst 1)) (succM M a)).
      apply code_graph_fresh_successor;reflexivity. }
    apply (HGeneric f).
    exact (proj1 (code_subst_graph M rho sigma
      (raw_domain_environment M w a (code_numeral M 1) z theta c) HSigma E_raw_domain_statement f) Hf). }
  assert (HRebind:ns_proof M rho (E_wim specialized_marker_expression Emp)).
  { exact (numerical_empty_rebind M rho (CEconst 1) (CEconst 2) (CEvar 3)
      (code_numeral M 1) (code_numeral M 2) z eq_refl eq_refl eq_refl
      (not_eq_sym (separation_lt_neq M (zeroM M) (code_numeral M 2)
        (proj2 (fixed_source_numeral_lt_iff M 0 2) ltac:(lia))))
      (not_eq_sym (separation_lt_neq M (zeroM M) z H0z))
      (separation_lt_neq M (code_numeral M 2) z H2z)
      (separation_lt_neq M (code_numeral M 1) (code_numeral M 2) (coding_lt_succ M _))
      (separation_lt_neq M (code_numeral M 1) z H1z)). }
  assert (HM:code_relation M rho specialized_marker_expression marker).
  { change (code_relation M rho (code_subst (fun _=>CEconst 0) specialized_marker_expression) marker).
    apply (proj2 (code_subst_graph M rho (fun _=>CEconst 0) (fun _=>zeroM M)
      ltac:(intro idx;reflexivity) specialized_marker_expression marker)). exact HMarker. }
  assert (HO:code_relation M rho Target out).
  { change (code_relation M rho (code_subst
      (fun idx=>match idx with 0=>CEvar 0|1=>CEvar 1|2=>CEvar 2|_=>CEconst 0 end) Target) out).
    apply (proj2 (code_subst_graph M rho
      (fun idx=>match idx with 0=>CEvar 0|1=>CEvar 1|2=>CEvar 2|_=>CEconst 0 end)
      (raw_separation_parameters M a w theta) ltac:(intros [|[|[|idx]]];reflexivity) Target out)).
    exact HOut. }
  destruct (code_relation_total M Emp rho) as [empty HE].
  exact (numerical_implies_trans M marker empty out
    (proj1 (numerical_implies_expression M rho specialized_marker_expression Emp marker empty HM HE) HRebind)
    (proj1 (numerical_implies_expression M rho Emp Target empty out HE HO) HInstance)).
Qed.

Print Assumptions actual_raw_domain_separation_certificates.
