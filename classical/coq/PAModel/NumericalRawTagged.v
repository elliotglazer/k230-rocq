(** Full raw three-branch comprehension. The pair seed, KP0 container,
    and singleton query witnesses are constructed numerically and discharged. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps FreshNames NamedBinderFresh TemplateFormulaFresh
  NumericalVacuitySteps NumericalKP0Eligibility NumericalKP0 NumericalKP0Requests
  NumericalSingleton NumericalRawPair NumericalFreshPair NumericalFreshSingleton
  NumericalTaggedComprehension NumericalTaggedExactKernel TaggedKernelUpgrade
  TaggedSelectedAllocation RawMarkerExclusions RawMarkerQuantifiers
  BoundVariableVacuityRules TemplatePropositional ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From FOL.Tennenbaum Require Import Peano.
Import ListNotations.
Unset Implicit Arguments.

Definition raw_tagged_parameters M y box marker theta z k idx : carrier M :=
  match idx with 0=>y|3=>box|4=>marker|6=>k|7=>z|8=>theta|_=>zeroM M end.
Definition E_raw_tagged_statement :=
  E_wim (E_marker_empty (CEvar 4) (CEvar 7))
    (E_wim (E_wn (E_weq (CEvar 3) (CEvar 4)))
      (E_wex (CEvar 6) E_tagged_upgrade_exact)).
Definition raw_tagged_roles M y box marker z idx : carrier M :=
  match idx with 0=>y|1=>box|2=>marker|_=>z end.

Theorem numerical_raw_tagged_comprehension M y box marker theta z :
  (forall i j,i<4 -> j<4 -> i<>j ->
    raw_tagged_roles M y box marker z i<>raw_tagged_roles M y box marker z j) ->
  (forall i,i<4 -> raw_tagged_roles M y box marker z i<>zeroM M) ->
  named_binder_absent M theta marker ->
  exists k f,code_relation M (raw_tagged_parameters M y box marker theta z k)
    E_raw_tagged_statement f /\ numerically_provable M f.
Proof.
  intros D N HT.
  pose proof (D 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) as DYB.
  pose proof (D 0 2 ltac:(lia) ltac:(lia) ltac:(lia)) as DYT.
  pose proof (D 0 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DYZ.
  pose proof (D 1 2 ltac:(lia) ltac:(lia) ltac:(lia)) as DBT.
  pose proof (D 1 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DBZ.
  pose proof (D 2 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DTZ.
  pose proof (N 0 ltac:(lia)) as NY. pose proof (N 1 ltac:(lia)) as NB.
  pose proof (N 2 ltac:(lia)) as NT. pose proof (N 3 ltac:(lia)) as NZ.
  set (names:=[zeroM M;y;box;marker;z;theta]).
  set (base:=finite_name_bound M names).
  set (r:=succM M (succM M base)). set (input:=succM M r).
  assert (Bound:forall v,In v names -> coding_lt M v base).
  { intros v Hv. apply finite_name_bound_above,Hv. }
  assert (BR:coding_lt M base r) by (eapply coding_lt_trans;apply coding_lt_succ).
  assert (RI:coding_lt M r input) by apply coding_lt_succ.
  assert (LT:forall v,In v names -> coding_lt M v r).
  { intros v Hv. exact (coding_lt_trans M v base r (Bound v Hv) BR). }
  assert (LI:forall v,In v names -> coding_lt M v input).
  { intros v Hv. exact (coding_lt_trans M v r input (LT v Hv) RI). }
  assert (RY:y<>r) by (apply fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (RB:box<>r) by (apply fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (RT:marker<>r) by (apply fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (RZ:z<>r) by (apply fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (IY:y<>input) by (apply fresh_singleton_lt_neq,LI;unfold names;cbn;tauto).
  assert (IB:box<>input) by (apply fresh_singleton_lt_neq,LI;unfold names;cbn;tauto).
  assert (IT:marker<>input) by (apply fresh_singleton_lt_neq,LI;unfold names;cbn;tauto).
  assert (IZ:z<>input) by (apply fresh_singleton_lt_neq,LI;unfold names;cbn;tauto).
  assert (DRI:r<>input) by (apply fresh_singleton_lt_neq,RI).
  assert (NR:r<>zeroM M) by (apply not_eq_sym,fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (NI:input<>zeroM M) by (apply not_eq_sym,fresh_singleton_lt_neq,LI;unfold names;cbn;tauto).
  assert (DS:forall i j,i<6 -> j<6 -> i<>j ->
    tagged_seed_roles M input y box marker r z i <> tagged_seed_roles M input y box marker r z j).
  { intros i j Hi Hj Hij. destruct i as [|[|[|[|[|[|i]]]]]];
      destruct j as [|[|[|[|[|[|j]]]]]];cbn [tagged_seed_roles raw_tagged_roles] in *;try lia;congruence. }
  assert (NS:forall i,i<6 -> tagged_seed_roles M input y box marker r z i<>zeroM M).
  { intros i Hi. destruct i as [|[|[|[|[|[|i]]]]]];cbn [tagged_seed_roles raw_tagged_roles] in *;try lia;congruence. }
  assert (FInput:formula_fresh M theta input).
  { apply formula_above_is_fresh,LI. unfold names;cbn;tauto. }
  assert (FRoot:formula_fresh M theta r).
  { apply formula_above_is_fresh,LT. unfold names;cbn;tauto. }
  destruct (numerical_tagged_exact_kernel M input y box marker r theta z DS NS FInput
    (named_formula_fresh_binder_absent M theta r FRoot) HT) as (k & q & f & HF & PF).
  set (rho:=tagged_exact_environment M input y box marker r theta z k q).
  set (Emp:=E_marker_empty (CEvar 4) (CEvar 7)).
  set (Neq:=E_wn (E_weq (CEvar 3) (CEvar 4))).
  set (Pair:=E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7)).
  set (Out:=E_wex (CEvar 6) E_tagged_upgrade_exact).
  set (Target:=E_wim Emp (E_wim Neq Out)).
  assert (HExact:ns_proof M rho (E_wim (E_wa Emp (E_wa Neq Pair)) Out)).
  { intros v Hv. assert (v=f) by (eapply code_relation_functional;eassumption). now subst v. }
  assert (HPoint:ns_proof M rho (E_wim Pair Target)).
  { apply (ns_proof_macro M rho (E_wim (E_wa Emp (E_wa Neq Pair)) Out :: nil)).
    - intros e [<-|[]]. exact HExact.
    - apply macro_discharge. do 3 apply macro_deduction.
      eapply md_mp with (a:=E_wa Emp (E_wa Neq Pair)).
      + apply kp0_md_conjunction;[apply md_hyp;now right;left|].
        apply kp0_md_conjunction;apply md_hyp;cbn;tauto.
      + apply md_global,PM_input;now left. }
  assert (HOutV:ns_proof M rho (E_vac (CEvar 5) Out)).
  { destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho0=>axioms M ax rho0 H) k r) as [Ekr|Ekr].
    - subst k. change (ns_proof M rho (E_vac (CEvar 6) (E_wex (CEvar 6) E_tagged_upgrade_exact))).
      apply ns_bound_existential_vacuity.
    - apply (kp0_expression_fresh_vacuity M rho (CEvar 5) Out r eq_refl).
      unfold Out,E_tagged_upgrade_exact,E_tagged_exact.
      apply expression_fresh_existential;[exact NR| |].
      + exact (marker_name_avoids M rho (CEvar 6) k r eq_refl Ekr).
      + apply expression_fresh_universal.
        * exact (marker_name_avoids M rho (CEvar 0) y r eq_refl RY).
        * apply expression_fresh_conjunction;[exact NR| |];apply expression_fresh_implication.
          -- apply expression_fresh_atom;[now left| |].
             ++ exact (marker_name_avoids M rho (CEvar 0) y r eq_refl RY).
             ++ exact (marker_name_avoids M rho (CEvar 6) k r eq_refl Ekr).
          -- apply tagged_profile_fresh;try exact NR.
             ++ exact (marker_name_avoids M rho (CEvar 0) y r eq_refl RY).
             ++ exact (marker_name_avoids M rho (CEvar 3) box r eq_refl RB).
             ++ exact (marker_name_avoids M rho (CEvar 4) marker r eq_refl RT).
             ++ intros v Hv. change (v=theta) in Hv. now subst v.
          -- apply tagged_profile_fresh;try exact NR.
             ++ exact (marker_name_avoids M rho (CEvar 0) y r eq_refl RY).
             ++ exact (marker_name_avoids M rho (CEvar 3) box r eq_refl RB).
             ++ exact (marker_name_avoids M rho (CEvar 4) marker r eq_refl RT).
             ++ intros v Hv. change (v=theta) in Hv. now subst v.
          -- apply expression_fresh_atom;[now left| |].
             ++ exact (marker_name_avoids M rho (CEvar 0) y r eq_refl RY).
             ++ exact (marker_name_avoids M rho (CEvar 6) k r eq_refl Ekr). }
  assert (HEmpV:ns_proof M rho (E_vac (CEvar 5) Emp)).
  { apply (kp0_expression_fresh_vacuity M rho (CEvar 5) Emp r eq_refl).
    exact (marker_empty_fresh M rho (CEvar 4) (CEvar 7) marker z r eq_refl eq_refl NR RT RZ). }
  assert (HNeqV:ns_proof M rho (E_vac (CEvar 5) Neq)).
  { apply (kp0_expression_fresh_vacuity M rho (CEvar 5) Neq r eq_refl).
    apply expression_fresh_negation;[exact NR|]. apply expression_fresh_atom;[now right| |].
    - exact (marker_name_avoids M rho (CEvar 3) box r eq_refl RB).
    - exact (marker_name_avoids M rho (CEvar 4) marker r eq_refl RT). }
  assert (HV:ns_proof M rho (E_vac (CEvar 5) Target)).
  { apply (ns_proof_macro M rho
      (E_vac (CEvar 5) Emp :: E_vac (CEvar 5) Neq :: E_vac (CEvar 5) Out :: nil)).
    - intros e [<-|[<-|[<-|[]]]];assumption.
    - apply macro_vacuous_implication;[apply PM_input;now left|].
      apply macro_vacuous_implication;apply PM_input;cbn;tauto. }
  set (rhof:=fun i=>if Nat.eq_dec i 11 then base else rho i).
  assert (HpairF:ns_proof M rhof (E_wex (CEvar 5) Pair)).
  { apply (numerical_fresh_pair M rhof (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7) (CEvar 11)
      box marker r z base eq_refl eq_refl eq_refl eq_refl eq_refl DBZ DTZ NZ eq_refl).
    - apply Bound;unfold names;cbn;tauto.
    - apply Bound;unfold names;cbn;tauto.
    - apply Bound;unfold names;cbn;tauto.
    - apply Bound;unfold names;cbn;tauto. }
  assert (Hpair:ns_proof M rho (E_wex (CEvar 5) Pair)).
  { change (ns_proof M rho (E_wex (CEvar 5) Pair)) in HpairF. exact HpairF. }
  assert (P:ns_proof M rho Target).
  { apply (ns_proof_macro M rho (E_wim Pair Target :: E_vac (CEvar 5) Target :: E_wex (CEvar 5) Pair :: nil)).
    - intros e [<-|[<-|[<-|[]]]];assumption.
    - eapply PM_mp;[apply PM_input;now right;right;left|].
      apply kp0_exists_eliminate;apply PM_input;cbn;tauto. }
  change (ns_proof M (raw_tagged_parameters M y box marker theta z k) E_raw_tagged_statement) in P.
  destruct (code_relation_total M E_raw_tagged_statement (raw_tagged_parameters M y box marker theta z k))
    as [result HResult].
  exists k,result. split;[exact HResult|exact (P result HResult)].
Qed.

Print Assumptions numerical_raw_tagged_comprehension.
