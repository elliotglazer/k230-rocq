(** Consume the actual uniform numerical KP0 kernel. Pair and empty-marker
    assumptions remain object formulas; there is no assumed kernel witness. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions
  NumericalProofs ProofTemplates CodeDescent QuotientAtomTemplates NamedLeibnizSteps FreshNames FreshPropagation
  NamedBinderFresh TemplateFormulaFresh ExpressionFreshElimination
  NumericalTaggedMatrix TaggedMatrixSubstitution NumericalTaggedComprehension
  NumericalTaggedKernel TaggedKernelUpgrade TaggedUniversalSelected
  TaggedSelectedAllocation NumericalKP0 ProofMacros.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Definition tagged_seed_roles M input y box marker root z idx : carrier M :=
  match idx with 0=>y|1=>input|2=>box|3=>marker|4=>root|_=>z end.
Definition tagged_exact_environment M input y box marker root theta z k q idx : carrier M :=
  match idx with 0=>y|1=>input|3=>box|4=>marker|5=>root|6=>k|7=>z|8=>theta|10=>q|_=>zeroM M end.

Lemma tagged_matrix_fresh_nonzero M rho name y input box marker root theta z :
  expression_fresh M rho name (E_tagged_matrix y input box marker root theta z) ->
  name<>zeroM M.
Proof.
  intro HF. unfold E_tagged_matrix,E_tagged_choices,E_or in HF.
  pose proof (proj1 (expression_fresh_implication_parts M rho name _ _ HF)) as HNeg.
  pose proof (proj2 (expression_fresh_implication_parts M rho name _ _ HNeg)) as HOne.
  assert (HG:membership_graph M (zeroM M) (zeroM M) (code_numeral M 1)).
  { exists (zeroM M). split;[apply pair_zero|].
    rewrite (Arithmetic.mul_comm M),Arithmetic.mul_zero,Arithmetic.add_zero. reflexivity. }
  pose proof (proj1 (formula_fresh_membership M (zeroM M) (zeroM M)
    (code_numeral M 1) name HG (HOne _ eq_refl))) as H.
  congruence.
Qed.

Theorem numerical_tagged_exact_kernel M input y box marker root theta z :
  (forall i j,i<6 -> j<6 -> i<>j ->
    tagged_seed_roles M input y box marker root z i <>
    tagged_seed_roles M input y box marker root z j) ->
  (forall i,i<6 -> tagged_seed_roles M input y box marker root z i<>zeroM M) ->
  formula_fresh M theta input -> named_binder_absent M theta root ->
  named_binder_absent M theta marker ->
  exists k q f,
    code_relation M (tagged_exact_environment M input y box marker root theta z k q)
      (E_wim E_tagged_upgrade_antecedent (E_wex (CEvar 6) E_tagged_upgrade_exact)) f /\
    numerically_provable M f.
Proof.
  intros DS NS HTheta HRoot HMarker.
  pose proof (NS 0 ltac:(lia)) as N_0.
  pose proof (DS 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) as D_0_1.
  pose proof (DS 0 2 ltac:(lia) ltac:(lia) ltac:(lia)) as D_0_2.
  pose proof (DS 0 3 ltac:(lia) ltac:(lia) ltac:(lia)) as D_0_3.
  pose proof (DS 0 4 ltac:(lia) ltac:(lia) ltac:(lia)) as D_0_4.
  pose proof (DS 0 5 ltac:(lia) ltac:(lia) ltac:(lia)) as D_0_5.
  pose proof (NS 1 ltac:(lia)) as N_1.
  pose proof (DS 1 2 ltac:(lia) ltac:(lia) ltac:(lia)) as D_1_2.
  pose proof (DS 1 3 ltac:(lia) ltac:(lia) ltac:(lia)) as D_1_3.
  pose proof (DS 1 4 ltac:(lia) ltac:(lia) ltac:(lia)) as D_1_4.
  pose proof (DS 1 5 ltac:(lia) ltac:(lia) ltac:(lia)) as D_1_5.
  pose proof (NS 2 ltac:(lia)) as N_2.
  pose proof (DS 2 3 ltac:(lia) ltac:(lia) ltac:(lia)) as D_2_3.
  pose proof (DS 2 4 ltac:(lia) ltac:(lia) ltac:(lia)) as D_2_4.
  pose proof (DS 2 5 ltac:(lia) ltac:(lia) ltac:(lia)) as D_2_5.
  pose proof (NS 3 ltac:(lia)) as N_3.
  pose proof (DS 3 4 ltac:(lia) ltac:(lia) ltac:(lia)) as D_3_4.
  pose proof (DS 3 5 ltac:(lia) ltac:(lia) ltac:(lia)) as D_3_5.
  pose proof (NS 4 ltac:(lia)) as N_4.
  pose proof (DS 4 5 ltac:(lia) ltac:(lia) ltac:(lia)) as D_4_5.
  pose proof (NS 5 ltac:(lia)) as N_5.
  destruct (code_relation_total M
    (E_tagged_matrix (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6))
    (tagged_matrix_parameters M input y box marker root theta z)) as [m HM].
  destruct (numerical_tagged_kernel M input y box marker root theta z m
    N_1 D_0_1 (not_eq_sym D_1_2) (not_eq_sym D_1_3) (not_eq_sym D_1_4)
    D_0_4 (not_eq_sym D_1_5) (not_eq_sym D_4_5) HTheta HRoot HM)
    as (k & q & f & HKI & HKY & HKR & HIQ & HYQ & HKQ & HQR & HQ0 & HFK & HFQ & Hf & Pf).
  set (matrixrho:=tagged_matrix_parameters M input y box marker root theta z).
  set (matrix:=E_tagged_matrix (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6)).
  assert (FK:expression_fresh M matrixrho k matrix).
  { intros v Hv. assert (v=m) by (eapply code_relation_functional;eassumption). now subst v. }
  assert (FQ:expression_fresh M matrixrho q matrix).
  { intros v Hv. assert (v=m) by (eapply code_relation_functional;eassumption). now subst v. }
  pose proof (tagged_matrix_fresh_nonzero M matrixrho k (CEvar 1) (CEvar 0) (CEvar 2)
    (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) FK) as HK0.
  destruct (tagged_matrix_fresh_parts M matrixrho k (CEvar 1) (CEvar 0) (CEvar 2)
    (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) FK) as (KI & KR & KY & KB & KT & KZ & KTheta).
  destruct (tagged_matrix_fresh_parts M matrixrho q (CEvar 1) (CEvar 0) (CEvar 2)
    (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) FQ) as (QI & QR & QY & QB & QT & QZ & QTheta).
  specialize (KB box eq_refl). specialize (KT marker eq_refl). specialize (KZ z eq_refl).
  specialize (QB box eq_refl). specialize (QT marker eq_refl). specialize (QZ z eq_refl).
  specialize (QTheta theta eq_refl).
  set (rho:=tagged_exact_environment M input y box marker root theta z k q).
  assert (D:selected_fixed_roles_distinct M rho).
  { intros i j Hi Hj Hi2 Hj2 Hij.
    destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]];
      destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]];
      cbn [selected_query_role rho tagged_exact_environment tagged_seed_roles] in *;try lia;congruence. }
  assert (N:selected_fixed_roles_nonzero M rho).
  { intros i Hi Hi2. destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]];
      cbn [selected_query_role rho tagged_exact_environment tagged_seed_roles] in *;try lia;congruence. }
  change (code_relation M rho (E_wex (CEvar 6) E_tagged_upgrade_payload) f) in Hf.
  assert (HK:ns_proof M rho (E_wex (CEvar 6) E_tagged_upgrade_payload)).
  { intros v Hv. assert (v=f) by (eapply code_relation_functional;eassumption). now subst v. }
  pose proof (numerical_tagged_kernel_lift M rho D N QTheta HRoot HMarker) as HL.
  assert (P:ns_proof M rho
    (E_wim E_tagged_upgrade_antecedent (E_wex (CEvar 6) E_tagged_upgrade_exact))).
  { apply (ns_proof_macro M rho
      (E_wex (CEvar 6) E_tagged_upgrade_payload ::
       E_wim E_tagged_upgrade_antecedent
         (E_wim (E_wex (CEvar 6) E_tagged_upgrade_payload)
           (E_wex (CEvar 6) E_tagged_upgrade_exact)) :: nil)).
    - intros e [<-|[<-|[]]];assumption.
    - apply macro_discharge,macro_deduction.
      eapply md_mp with (a:=E_wex (CEvar 6) E_tagged_upgrade_payload).
      + apply md_global,PM_input;now left.
      + eapply md_mp with (a:=E_tagged_upgrade_antecedent);[apply md_hyp;now left|].
        apply md_global,PM_input;now right;left. }
  destruct (code_relation_total M
    (E_wim E_tagged_upgrade_antecedent (E_wex (CEvar 6) E_tagged_upgrade_exact)) rho) as [result HR].
  exists k,q,result. split;[exact HR|exact (P result HR)].
Qed.

Print Assumptions numerical_tagged_exact_kernel.
