(** Protect the original matrix names, including names erased by a prior
    substitution, by a proved tautological conjunct before choosing K names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates TemplateCD TemplatePropositional ProofMacros QuantifierMacros NamedLeibnizSteps NumericalBootstrap
  NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility KP0SeedSpecialization KP0MatrixTransport
  TemplateBinderFresh TemplateNamedSubstitution TemplateFormulaFresh
  NamedBinderFresh NamedSubstitution NamedSubstitutionFunctionality FreshNames
  FreshSubstitutionIdentity ExpressionFreshElimination NumericalTaggedMatrix CollectionAvoidingKernel.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_collection_protected_kp0 M i v root x q d m original :
  i<>zeroM M -> v<>i -> i<>root -> v<>root -> x<>i -> q<>i -> d<>i ->
  named_binder_absent M m i -> named_binder_absent M m root -> formula_mentions M m root ->
  formula_fresh M original i -> named_binder_absent M original root ->
  exists k p mp f,
    k<>i /\ k<>v /\ k<>root /\ i<>p /\ v<>p /\ k<>p /\ p<>root /\ p<>zeroM M /\
    k<>x /\ k<>q /\ k<>d /\ p<>x /\ p<>q /\ p<>d /\
    formula_fresh M m k /\ formula_fresh M m p /\
    formula_fresh M original k /\ formula_fresh M original p /\
    named_substitution M m i p mp /\
    code_relation M (kp0_seed_parameters M i v k p m mp root)
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f /\
    numerically_provable M f.
Proof.
  intros H0 HVI HIR HVR HXI HQI HDI HMI HMR Hmention HOrigI HOrigR.
  set (r0:=original .: m .: fun _=>zeroM M).
  set (Pad:=E_wa (E_wim (CEvar 0) (CEvar 0)) (CEvar 1)).
  destruct (code_relation_total M Pad r0) as [pad Hpad].
  assert (pad_absent:forall name,named_binder_absent M original name -> named_binder_absent M m name ->
      named_binder_absent M pad name).
  { intros name HO HM. apply (expression_binder_absent_conjunction M r0 name
      (E_wim (CEvar 0) (CEvar 0)) (CEvar 1)).
    - apply expression_binder_absent_implication;intros f Hf;change (f=original) in Hf;now subst f.
    - intros f Hf;change (f=m) in Hf;now subst f.
    - exact Hpad. }
  assert (HPmention:formula_mentions M pad root).
  { apply (collection_mentions_conjunction_right M r0 root (E_wim (CEvar 0) (CEvar 0)) (CEvar 1));
      [intros f Hf;change (f=m) in Hf;now subst f|exact Hpad]. }
  destruct (numerical_collection_avoiding_kp0 M i v root x q d pad H0 HVI HIR HVR HXI HQI HDI
      (pad_absent i (named_formula_fresh_binder_absent M original i HOrigI) HMI)
      (pad_absent root HOrigR HMR) HPmention)
    as (k&p&padp&old&HKI&HKV&HKR&HIP&HVP&HKP&HPR&HP0&HKX&HKQ&HKD&HPX&HPQ&HPD&FK&FP&HSub&HOld&POld).
  assert (pad_fresh:forall name,formula_fresh M pad name ->
      formula_fresh M original name /\ formula_fresh M m name).
  { intros name HF. assert (HE:expression_fresh M r0 name Pad).
    { intros f Hf. rewrite (code_relation_functional M Pad r0 f pad Hf Hpad). exact HF. }
    apply expression_fresh_conjunction_parts in HE. destruct HE as [HO HM].
    apply expression_fresh_implication_parts in HO. destruct HO as [HO _].
    split;[exact (HO original eq_refl)|exact (HM m eq_refl)]. }
  destruct (pad_fresh k FK) as [FOK FMK]. destruct (pad_fresh p FP) as [FOP FMP].
  destruct (named_substitution_fresh_total M m i p FMP) as [mp HS].
  set (rho:=i .: v .: k .: p .: m .: mp .: root .: original .: fun _=>zeroM M).
  set (F:=E_wa (E_wim (CEvar 7) (CEvar 7)) (CEvar 4)).
  set (Fp:=E_wa (E_wim (CEvar 7) (CEvar 7)) (CEvar 5)).
  assert (HF:code_relation M rho F pad) by exact Hpad.
  destruct (code_relation_total M Fp rho) as [padp' HFp].
  assert (HOrigSub:expression_named_substitution M rho rho i p (CEvar 7) (CEvar 7)).
  { intros f g Hf Hg. change (f=original) in Hf. change (g=original) in Hg. subst f g.
    exact (named_substitution_source_fresh M original i p HOrigI (named_formula_fresh_binder_absent M original p FOP)). }
  assert (HSP:named_substitution M pad i p padp').
  { apply (expression_ns_conjunction M rho rho i p (E_wim (CEvar 7) (CEvar 7)) (CEvar 4)
      (E_wim (CEvar 7) (CEvar 7)) (CEvar 5) H0).
    - apply expression_ns_implication;exact HOrigSub.
    - intros f g Hf Hg. change (f=m) in Hf. change (g=mp) in Hg. now subst f g.
    - exact HF.
    - exact HFp. }
  assert (E:padp=padp') by exact (named_substitution_functional M pad i p padp padp' HSub HSP).
  subst padp'.
  set (repl:=CEvar 0 .: CEvar 1 .: CEvar 2 .: CEvar 3 .: F .: Fp .: CEvar 6 .: fun _=>CEconst 0).
  assert (HOld':code_relation M rho
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) F Fp) old).
  { assert (HR:forall j,code_relation M rho (repl j) (kp0_seed_parameters M i v k p pad padp root j)).
    { intros [|[|[|[|[|[|[|j]]]]]]];try reflexivity;assumption. }
    exact (proj2 (code_subst_graph M rho repl (kp0_seed_parameters M i v k p pad padp root) HR
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) old) HOld). }
  assert (PBefore:ns_proof M rho (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) F Fp)).
  { intros f Hf. rewrite (code_relation_functional M _ rho f old Hf HOld'). exact POld. }
  assert (PAfter:ns_proof M rho
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5))).
  { eapply ns_proof_mp;[exact PBefore|]. apply numerical_kp0_matrix_transport.
    - apply ns_proof_template,bootstrap_projection_right.
    - apply ns_proof_template,bootstrap_projection_right.
    - apply (ns_proof_macro M rho nil);[intros f []|].
      apply macro_discharge,macro_deduction,kp0_md_conjunction.
      + apply md_global,PM_template,template_I.
      + apply md_hyp;now left. }
  destruct (code_relation_total M
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) rho) as [f Hf].
  exists k,p,mp,f. repeat split;try assumption. exact (PAfter f Hf).
Qed.

Print Assumptions numerical_collection_protected_kp0.




