(** Choose outer Collection names after the actual substituted matrix and
    after each expression whose freshness must later be established. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  ProofTemplates NamedLeibnizSteps FreshNames NamedBinderFresh NamedSubstitution
  TemplateBinderFresh TemplateNamedSubstitution
  CollectionFreshAllocation CollectionOrderedNames RawMarkerExclusions
  RawCollectionProfile NumericalRawEnvelope.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition collection_closure_environment M t a c x v theta z q b idx : carrier M :=
  match idx with 0=>t|1=>a|2=>c|3=>x|4=>v|5=>theta|6=>z|7=>q|8=>b|_=>zeroM M end.
Definition E_collection_closure_goal :=
  E_wex (CEvar 2) (E_raw_collection_profile (CEvar 0) (CEvar 1)
    (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)).
Definition E_collection_closure_final :=
  E_wim (E_marker_empty (CEvar 0) (CEvar 6))
    (E_wim (E_wel (CEvar 0) (CEvar 1)) E_collection_closure_goal).
Definition E_collection_closure_step :=
  E_wim (E_raw_envelope (CEvar 0) (CEvar 1) (CEvar 8) (CEvar 7))
    E_collection_closure_final.

Record collection_outer_allocation M t a c x v theta := {
  coa_w : carrier M;
  coa_thetaW : carrier M;
  coa_j : carrier M;
  coa_z : carrier M;
  coa_q : carrier M;
  coa_b : carrier M;
  coa_r : carrier M;
  coa_baseB : carrier M;
  coa_baseR : carrier M;
  coa_final : carrier M;
  coa_step : carrier M;
  coa_distinct : NoDup [t;a;coa_b;coa_r;coa_j;x;coa_w;v;coa_z;coa_q;c];
  coa_w_nonzero : coa_w<>zeroM M;
  coa_j_nonzero : coa_j<>zeroM M;
  coa_z_nonzero : coa_z<>zeroM M;
  coa_q_nonzero : coa_q<>zeroM M;
  coa_substitution : named_substitution M theta x coa_w coa_thetaW;
  coa_thetaW_j_fresh : formula_fresh M coa_thetaW coa_j;
  coa_thetaW_r_absent : named_binder_absent M coa_thetaW coa_r;
  coa_theta_w_fresh : formula_fresh M theta coa_w;
  coa_theta_j_fresh : formula_fresh M theta coa_j;
  coa_theta_r_absent : named_binder_absent M theta coa_r;
  coa_b_equation : coa_b=succM M (succM M coa_baseB);
  coa_r_equation : coa_r=succM M (succM M coa_baseR);
  coa_baseB_bounds : forall n,In n [zeroM M;t;a;coa_q;coa_z] -> coding_lt M n coa_baseB;
  coa_baseR_bounds : forall n,In n [zeroM M;coa_b;t;coa_z] -> coding_lt M n coa_baseR;
  coa_final_graph : code_relation M
    (collection_closure_environment M t a c x v theta coa_z coa_q coa_b)
    E_collection_closure_final coa_final;
  coa_step_graph : code_relation M
    (collection_closure_environment M t a c x v theta coa_z coa_q coa_b)
    E_collection_closure_step coa_step;
  coa_final_b_fresh : formula_fresh M coa_final coa_b;
  coa_step_r_fresh : formula_fresh M coa_step coa_r
}.

Theorem collection_outer_allocation_total M t a c x v theta :
  NoDup [t;a;c;x;v] -> named_binder_absent M theta x -> named_binder_absent M theta v ->
  inhabited (collection_outer_allocation M t a c x v theta).
Proof.
  intros ND HX HV.
  set (fixed:=[zeroM M;t;a;c;theta;x;v]).
  destruct (collection_fresh_witness_allocation M theta x v fixed HX HV)
    as (w&thetaW&j&z&q&HW&FreshW&Sub&AbsX&AbsV&HJ&HJZ&HZQ&FreshJ&FreshZ&FreshQ).
  set (rho0:=collection_closure_environment M t a c x v theta z q (zeroM M)).
  destruct (code_relation_total M E_collection_closure_final rho0) as [g HG].
  set (namesB:=[zeroM M;t;a;c;x;v;w;j;z;q;theta;thetaW;g]).
  set (baseB:=collection_name_bound M namesB).
  set (b:=succM M (succM M baseB)).
  assert (BB:forall n,In n namesB -> coding_lt M n baseB).
  { intros n Hn;apply collection_name_bound_above,Hn. }
  assert (BBb:coding_lt M baseB b) by (eapply coding_lt_trans;apply coding_lt_succ).
  set (rho:=collection_closure_environment M t a c x v theta z q b).
  assert (HG':code_relation M rho E_collection_closure_final g).
  { change (code_relation M rho0 E_collection_closure_final g). exact HG. }
  destruct (code_relation_total M E_collection_closure_step rho) as [h HH].
  set (namesR:=[zeroM M;t;a;c;x;v;w;j;z;q;theta;thetaW;g;b;h]).
  set (baseR:=collection_name_bound M namesR).
  set (r:=succM M (succM M baseR)).
  assert (BR:forall n,In n namesR -> coding_lt M n baseR).
  { intros n Hn;apply collection_name_bound_above,Hn. }
  assert (BRr:coding_lt M baseR r) by (eapply coding_lt_trans;apply coding_lt_succ).
  assert (LowW:forall n,In n [zeroM M;t;a;c;x;v;theta] -> coding_lt M n w).
  { intros n Hn. apply HW. unfold fixed in *. cbn in *;tauto. }
  assert (WJ:coding_lt M w j) by (apply HJ;now right;left).
  assert (LowJ:forall n,In n [zeroM M;theta] -> coding_lt M n j).
  { intros n Hn. apply HJ. unfold fixed in *;cbn in *;tauto. }
  assert (QB:coding_lt M q b).
  { eapply coding_lt_trans;[apply BB;unfold namesB;cbn;tauto|exact BBb]. }
  assert (BRlt:coding_lt M b r).
  { eapply coding_lt_trans;[apply BR;unfold namesR;cbn;tauto|exact BRr]. }
  constructor. refine ({|
    coa_w:=w;coa_thetaW:=thetaW;coa_j:=j;coa_z:=z;coa_q:=q;coa_b:=b;coa_r:=r;
    coa_baseB:=baseB;coa_baseR:=baseR;coa_final:=g;coa_step:=h
  |}).
  - apply (collection_ordered_names_nodup M t a c x v w j z q b r ND);
      try assumption;apply LowW;cbn;tauto.
  - apply template_lt_different,LowW;now left.
  - apply template_lt_different,LowJ;now left.
  - apply template_lt_different. eapply coding_lt_trans;[apply LowJ;now left|exact HJZ].
  - apply template_lt_different. eapply coding_lt_trans;[apply LowJ;now left|].
    exact (coding_lt_trans M j z q HJZ HZQ).
  - exact Sub.
  - exact FreshJ.
  - apply named_formula_fresh_binder_absent,formula_above_is_fresh.
    eapply coding_lt_trans;[apply BR;unfold namesR;cbn;tauto|exact BRr].
  - exact FreshW.
  - apply formula_above_is_fresh,LowJ;cbn;tauto.
  - apply named_formula_fresh_binder_absent,formula_above_is_fresh.
    eapply coding_lt_trans;[apply BR;unfold namesR;cbn;tauto|exact BRr].
  - reflexivity.
  - reflexivity.
  - intros n Hn;apply BB. unfold namesB;cbn in *;tauto.
  - intros n Hn;apply BR. unfold namesR;cbn in *;tauto.
  - exact HG'.
  - exact HH.
  - apply formula_above_is_fresh.
    eapply coding_lt_trans;[apply BB;unfold namesB;cbn;tauto|exact BBb].
  - apply formula_above_is_fresh.
    eapply coding_lt_trans;[apply BR;unfold namesR;cbn;tauto|exact BRr].
Qed.

Print Assumptions collection_outer_allocation_total.
