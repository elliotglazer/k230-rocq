(** A raw singleton constructor from the actual numerical K core. Its
    constant-output matrix does not require seed substitution. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates TemplatePropositional ProofMacros QuantifierMacros
  NumericalVacuitySteps NumericalEquality NamedLeibnizSteps NamedAlpha NamedExistential
  NumericalKP0 NumericalKP0Eligibility NumericalKP0Requests NumericalTaggedComprehension
  TemplateFormulaFresh FreshNames NumericalBootstrap TemplateBinderFresh
  TemplateNamedSubstitution NamedBinderFresh StoppingInstantiation.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_raw_singleton x k b :=
  E_wa (E_wel x k) (E_wal b (E_wim (E_wel b k) (E_weq b x))).

Definition singleton_seed_inputs a b k x :=
  E_vac a (E_weq b x) :: E_vac b (E_wel x k) ::
  E_wim (E_weq b x) (E_wim (E_wel b k) (E_wel x k)) :: nil.

Lemma singleton_seed_program a b k x :
  proof_macro nil (singleton_seed_inputs a b k x)
    (E_wim (E_kp_seed_root a b k (E_weq b x)) (E_wex k (E_raw_singleton x k b))).
Proof.
  set (inputs:=singleton_seed_inputs a b k x).
  assert (HW : proof_macro nil inputs
    (E_wim (E_wex b (E_wa (E_wel b k) (E_weq b x))) (E_wel x k))).
  { apply kp0_exists_eliminate.
    - apply PM_input;unfold inputs,singleton_seed_inputs;now right;left.
    - apply macro_discharge,macro_deduction.
      eapply md_mp with (a:=E_wel b k).
      + apply tagged_md_left with (b:=E_weq b x),md_hyp;now left.
      + eapply md_mp with (a:=E_weq b x).
        * apply tagged_md_right with (a:=E_wel b k),md_hyp;now left.
        * apply md_global,PM_input;unfold inputs,singleton_seed_inputs;now right;right;left. }
  assert (HS : proof_macro nil inputs
    (E_wim (E_kp_emitted a b k (E_weq b x))
      (E_wal b (E_wim (E_wel b k) (E_weq b x))))).
  { unfold E_kp_emitted. apply macro_all_monotone,kp0_implication_map.
    eapply macro_syl;[apply macro_exists_monotone,PM_template,bootstrap_projection_left|].
    apply request_existential_collapse,PM_input;unfold inputs,singleton_seed_inputs;now left. }
  unfold E_kp_seed_root,E_raw_singleton.
  apply macro_exists_monotone,macro_discharge,macro_deduction,kp0_md_conjunction.
  - eapply md_mp with (a:=E_wex b (E_wa (E_wel b k) (E_weq b x))).
    + eapply md_mp with (a:=E_wex b (E_weq b x)).
      * exact (md_global _ _ _ _ (PM_template _ (TP_row LR1 b x (CEconst 0) (CEconst 0)))).
      * apply tagged_md_left with (b:=E_kp_emitted a b k (E_weq b x)),md_hyp;now left.
    + apply md_global;exact HW.
  - eapply md_mp with (a:=E_kp_emitted a b k (E_weq b x)).
    + apply tagged_md_right with
        (a:=E_wim (E_wex b (E_weq b x)) (E_wex b (E_wa (E_wel b k) (E_weq b x)))),md_hyp;now left.
    + apply md_global;exact HS.
Qed.

Theorem numerical_singleton_from_seed M rho a b k x av bv kv xv :
  code_relation M rho a av -> code_relation M rho b bv ->
  code_relation M rho k kv -> code_relation M rho x xv ->
  bv<>av -> xv<>av -> xv<>bv -> kv<>bv ->
  ns_proof M rho
    (E_wim (E_kp_seed_root a b k (E_weq b x)) (E_wex k (E_raw_singleton x k b))).
Proof.
  intros HA HB HK HX HBA HXA HXB HKB.
  apply (ns_proof_macro M rho (singleton_seed_inputs a b k x)).
  - intros e [<-|[<-|[<-|[]]]].
    + apply (kp0_expression_fresh_vacuity M rho a (E_weq b x) av HA).
      apply expression_fresh_atom;[now right| |].
      * intros v Hv. rewrite (code_relation_functional M b rho v bv Hv HB). exact HBA.
      * intros v Hv. rewrite (code_relation_functional M x rho v xv Hv HX). exact HXA.
    + apply (kp0_expression_fresh_vacuity M rho b (E_wel x k) bv HB).
      apply expression_fresh_atom;[now left| |].
      * intros v Hv. rewrite (code_relation_functional M x rho v xv Hv HX). exact HXB.
      * intros v Hv. rewrite (code_relation_functional M k rho v kv Hv HK). exact HKB.
    + apply numerical_tagged_membership_transport.
  - apply singleton_seed_program.
Qed.

Theorem numerical_singleton_named M a b x :
  a<>b -> a<>x -> b<>x ->
  exists k f, k<>a /\ k<>b /\
    code_relation M (code_parameters a b k x)
      (E_wex (CEvar 2) (E_raw_singleton (CEvar 3) (CEvar 2) (CEvar 1))) f /\
    numerically_provable M f.
Proof.
  intros HAB HAX HBX.
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 1))
    (arguments2 b x (zeroM M))) as [m HM].
  destruct (numerical_uniform_kp0_seed_unrestricted M a b m)
    as [k [seed [HKA [HKB [HFM [HS PS]]]]]].
  set (rho:=code_parameters a b k x).
  assert (HMatrix : code_relation M rho (E_weq (CEvar 1) (CEvar 3)) m).
  { apply (proj2 (expression_equality_graph M rho (CEvar 1) (CEvar 3) b x m eq_refl eq_refl)).
    exact (proj1 (expression_equality_graph M (arguments2 b x (zeroM M))
      (CEvar 0) (CEvar 1) b x m eq_refl eq_refl) HM). }
  assert (HSeed : code_relation M rho
    (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (E_weq (CEvar 1) (CEvar 3))) seed).
  { apply (proj2 (code_subst_graph M rho
      (code_parameters (CEvar 0) (CEvar 1) (CEvar 2) (E_weq (CEvar 1) (CEvar 3)))
      (code_parameters a b k m) (parameter_graphs M rho
        (CEvar 0) (CEvar 1) (CEvar 2) (E_weq (CEvar 1) (CEvar 3)) a b k m
        eq_refl eq_refl eq_refl HMatrix)
      (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) seed)). exact HS. }
  destruct (code_relation_total M
    (E_wex (CEvar 2) (E_raw_singleton (CEvar 3) (CEvar 2) (CEvar 1))) rho) as [f HF].
  exists k,f. split;[exact HKA|]. split;[exact HKB|]. split;[exact HF|].
  apply (ns_proof_mp M rho
    (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (E_weq (CEvar 1) (CEvar 3)))
    (E_wex (CEvar 2) (E_raw_singleton (CEvar 3) (CEvar 2) (CEvar 1))));[| |exact HF].
  - intros v Hv. assert (v=seed) by exact (code_relation_functional M _ _ v seed Hv HSeed).
    now subst v.
  - apply (numerical_singleton_from_seed M rho (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
      a b k x eq_refl eq_refl eq_refl eq_refl);congruence.
Qed.

Corollary numerical_singleton M x :
  exists a b k f, a<>b /\ a<>x /\ b<>x /\ k<>a /\ k<>b /\
    code_relation M (code_parameters a b k x)
      (E_wex (CEvar 2) (E_raw_singleton (CEvar 3) (CEvar 2) (CEvar 1))) f /\
    numerically_provable M f.
Proof.
  destruct (kp0_fresh_input_name M x x x x) as [a [HXA _]].
  destruct (kp0_fresh_input_name M a x x x) as [b [HAB [HXB _]]].
  assert (HAX:a<>x) by congruence. assert (HBX:b<>x) by congruence.
  destruct (numerical_singleton_named M a b x HAB HAX HBX) as [k [f [HKA [HKB [HF PF]]]]].
  exists a,b,k,f. repeat split;assumption.
Qed.

Theorem singleton_profile_specialization M rho z x y p zv xv yv pv :
  code_relation M rho z zv -> code_relation M rho x xv ->
  code_relation M rho y yv -> code_relation M rho p pv ->
  zv<>xv -> pv<>zv -> yv<>zv ->
  ns_proof M rho (E_wim (E_wal z (E_wim (E_wel z p) (E_weq z y)))
    (E_wim (E_wel x p) (E_weq x y))).
Proof.
  intros HZ HX HY HP HZX HPZ HYZ.
  set (F:=E_wim (E_wel z p) (E_weq z y)).
  set (V:=E_wim (E_wel x p) (E_weq x y)).
  destruct (code_relation_total M F rho) as [f HF].
  destruct (code_relation_total M V rho) as [v HV].
  assert (HAbs : named_binder_absent M f xv).
  { apply (expression_binder_absent_implication M rho xv (E_wel z p) (E_weq z y)).
    - apply expression_binder_absent_atom;now left.
    - apply expression_binder_absent_atom;now right.
    - exact HF. }
  assert (HRZ : expression_named_replace M rho rho zv xv z x).
  { intros u w HU HW. rewrite (code_relation_functional M z rho u zv HU HZ),
      (code_relation_functional M x rho w xv HW HX). now left. }
  assert (HRP : expression_named_replace M rho rho zv xv p p).
  { intros u w HU HW. rewrite (code_relation_functional M p rho u pv HU HP),
      (code_relation_functional M p rho w pv HW HP). now right. }
  assert (HRY : expression_named_replace M rho rho zv xv y y).
  { intros u w HU HW. rewrite (code_relation_functional M y rho u yv HU HY),
      (code_relation_functional M y rho w yv HW HY). now right. }
  assert (HSub : NamedSubstitution.named_substitution M f zv xv v).
  { apply (expression_ns_implication M rho rho zv xv (E_wel z p) (E_weq z y)
      (E_wel x p) (E_weq x y));try assumption.
    - apply (expression_ns_atom M rho rho zv xv false);assumption.
    - apply (expression_ns_atom M rho rho zv xv true);assumption. }
  exact (proj1 (ns_stopping_instantiation M rho z x F V zv xv f v
    HZ HX HF HV HZX HAbs HSub)).
Qed.

Theorem numerical_singleton_uniqueness M rho x y p z xv yv pv zv :
  code_relation M rho x xv -> code_relation M rho y yv ->
  code_relation M rho p pv -> code_relation M rho z zv ->
  zv<>xv -> pv<>zv -> yv<>zv ->
  ns_proof M rho (E_wim (E_wel x p) (E_wim (E_raw_singleton y p z) (E_weq y x))).
Proof.
  intros HX HY HP HZ HZX HPZ HYZ.
  apply (ns_proof_macro M rho
    (E_wim (E_wal z (E_wim (E_wel z p) (E_weq z y)))
       (E_wim (E_wel x p) (E_weq x y)) ::
     E_wim (E_weq x y) (E_weq y x) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (singleton_profile_specialization M rho z x y p zv xv yv pv HZ HX HY HP HZX HPZ HYZ).
    + apply ns_proof_symmetry.
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_weq x y).
    + eapply md_mp with (a:=E_wel x p);[apply md_hyp;cbn;tauto|].
      eapply md_mp with (a:=E_wal z (E_wim (E_wel z p) (E_weq z y))).
      * apply tagged_md_right with (a:=E_wel y p),md_hyp;now left.
      * apply md_global,PM_input;now left.
    + apply md_global,PM_input;now right;left.
Qed.

Theorem numerical_singleton_profile M rho x y p z xv yv pv zv :
  code_relation M rho x xv -> code_relation M rho y yv ->
  code_relation M rho p pv -> code_relation M rho z zv ->
  zv<>xv -> pv<>zv -> yv<>zv -> xv<>yv -> pv<>yv ->
  ns_proof M rho (E_wim (E_raw_singleton x p z)
    (E_wal y (E_wim (E_raw_singleton y p z) (E_weq y x)))).
Proof.
  intros HX HY HP HZ HZX HPZ HYZ HXY HPY.
  assert (HV : ns_proof M rho (E_vac y (E_wel x p))).
  { apply (kp0_expression_fresh_vacuity M rho y (E_wel x p) yv HY).
    apply expression_fresh_atom;[now left| |].
    - intros v Hv. rewrite (code_relation_functional M x rho v xv Hv HX). exact HXY.
    - intros v Hv. rewrite (code_relation_functional M p rho v pv Hv HP). exact HPY. }
  apply (ns_proof_macro M rho
    (E_vac y (E_wel x p) :: E_wim (E_wel x p) (E_wim (E_raw_singleton y p z) (E_weq y x)) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact HV.
    + exact (numerical_singleton_uniqueness M rho x y p z xv yv pv zv HX HY HP HZ HZX HPZ HYZ).
  - eapply macro_syl;[apply PM_template,bootstrap_projection_left|].
    eapply macro_syl;[apply PM_input;now left|].
    apply macro_all_monotone,PM_input;now right;left.
Qed.

Print Assumptions singleton_seed_program.
Print Assumptions numerical_singleton_named.
Print Assumptions numerical_singleton.
Print Assumptions numerical_singleton_uniqueness.
Print Assumptions numerical_singleton_profile.
