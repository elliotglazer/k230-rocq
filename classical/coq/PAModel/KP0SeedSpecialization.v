(** The free seed in KP0 can be specialized without changing the bound
    input role in its support clause or the already-substituted query body. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofClosure ProofTemplates NamedLeibnizSteps NamedSubstitution NamedSubstitutionRules
  NamedSubstitutionFunctionality NamedBinderFresh TemplateBinderFresh
  TemplateNamedSubstitution NamedExistential StoppingInstantiation
  NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility
  NamedSubstitutionPreservation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition E_kp_with_seed seed a b k p m mp :=
  E_wex k (E_wa (E_wal p (E_wim (E_kp_eligible seed b k p) (E_kp_request b k mp)))
    (E_kp_support_body a b k m)).
Lemma E_kp_with_seed_original a b k p m mp :
  E_kp_with_seed a a b k p m mp = E_kp_conclusion a b k p m mp.
Proof. reflexivity. Qed.

Definition kp0_seed_parameters M a b k p m mp r :=
  a .: b .: k .: p .: m .: mp .: r .: fun _=>zeroM M.

Lemma expression_ns_exists_stop M rho X F x y :
  code_relation M rho X x -> x<>zeroM M ->
  expression_named_substitution M rho rho x y (E_wex X F) (E_wex X F).
Proof.
  intros HX H0. unfold E_wex. apply expression_ns_negation;[exact H0|].
  intros f g HF HG. assert (f=g) by exact (code_relation_functional M _ rho f g HF HG).
  subst g. destruct (code_relation_total M (E_wn F) rho) as [h HH].
  apply (named_substitution_binder_stop M x h f y).
  apply universal_graph_tagged.
  exact (expression_universal_graph M rho X (E_wn F) x h f HX HH HF).
Qed.

Theorem kp0_seed_substitution M a b k p m mp r f g :
  a<>zeroM M -> a<>p -> b<>a -> k<>a -> a<>r ->
  b<>r -> k<>r -> p<>r ->
  named_binder_absent M m a -> named_binder_absent M m r ->
  named_substitution M m a p mp ->
  code_relation M (kp0_seed_parameters M a b k p m mp r)
    (E_kp_conclusion (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f ->
  code_relation M (kp0_seed_parameters M a b k p m mp r)
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) g ->
  named_substitution M f a r g.
Proof.
  intros H0 HAP HBA HKA HAR HBR HKR HPR HMA HMR HM HF HG.
  set (rho:=kp0_seed_parameters M a b k p m mp r).
  assert (HA : expression_named_replace M rho rho a r (CEvar 0) (CEvar 6)).
  { intros u v HU HV. change (u=a) in HU. change (v=r) in HV. subst u v. now left. }
  assert (HB : expression_named_replace M rho rho a r (CEvar 1) (CEvar 1)).
  { intros u v HU HV. change (u=b) in HU. change (v=b) in HV. subst u v. now right. }
  assert (HK : expression_named_replace M rho rho a r (CEvar 2) (CEvar 2)).
  { intros u v HU HV. change (u=k) in HU. change (v=k) in HV. subst u v. now right. }
  assert (HP : expression_named_replace M rho rho a r (CEvar 3) (CEvar 3)).
  { intros u v HU HV. change (u=p) in HU. change (v=p) in HV. subst u v. right;split;congruence. }
  assert (HMP : expression_named_substitution M rho rho a r (CEvar 5) (CEvar 5)).
  { intros u v HU HV. change (u=mp) in HU. change (v=mp) in HV. subst u v.
    exact (named_substitution_erases_source M m a p r mp HAP HMA HMR HM). }
  unfold E_kp_conclusion in HF. unfold E_kp_with_seed in HG.
  eapply (expression_ns_existential M rho rho a r (CEvar 2) (CEvar 2) _ _ k
    H0 eq_refl eq_refl HKA HKR);[|exact HF|exact HG].
  apply expression_ns_conjunction;[exact H0| |].
  - apply (expression_ns_universal M rho rho a r (CEvar 3) (CEvar 3) _ _ p
      eq_refl eq_refl ltac:(congruence) HPR).
    apply expression_ns_implication.
    + unfold E_kp_eligible. apply expression_ns_disjunction;[exact H0| |].
      * exact (expression_ns_atom M rho rho a r true _ _ _ _ HA HP).
      * apply (expression_ns_existential M rho rho a r (CEvar 1) (CEvar 1) _ _ b
          H0 eq_refl eq_refl HBA HBR).
        apply expression_ns_conjunction;[exact H0| |].
        -- exact (expression_ns_atom M rho rho a r false _ _ _ _ HB HK).
        -- unfold E_ksubset. apply (expression_ns_universal M rho rho a r
             (CEvar 2) (CEvar 2) _ _ k eq_refl eq_refl HKA HKR).
           apply expression_ns_implication;apply (expression_ns_atom M rho rho a r false);assumption.
    + unfold E_kp_request. apply expression_ns_implication.
      * exact (expression_ns_existential M rho rho a r (CEvar 1) (CEvar 1) _ _ b
          H0 eq_refl eq_refl HBA HBR HMP).
      * apply (expression_ns_existential M rho rho a r (CEvar 1) (CEvar 1) _ _ b
          H0 eq_refl eq_refl HBA HBR).
        apply expression_ns_conjunction;[exact H0| |exact HMP].
        exact (expression_ns_atom M rho rho a r false _ _ _ _ HB HK).
  - unfold E_kp_support_body. apply (expression_ns_universal M rho rho a r
      (CEvar 1) (CEvar 1) _ _ b eq_refl eq_refl HBA HBR).
    apply expression_ns_implication.
    + exact (expression_ns_atom M rho rho a r false _ _ _ _ HB HK).
    + apply (expression_ns_exists_stop M rho (CEvar 0) (CEvar 4) a r eq_refl H0).
Qed.

Lemma kp0_conclusion_binder_absent M a b k p m mp r f :
  a<>r -> b<>r -> k<>r -> p<>r ->
  named_binder_absent M m r -> named_binder_absent M mp r ->
  code_relation M (kp0_seed_parameters M a b k p m mp r)
    (E_kp_conclusion (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f ->
  named_binder_absent M f r.
Proof.
  intros HAR HBR HKR HPR HMR HMP.
  set (rho:=kp0_seed_parameters M a b k p m mp r).
  assert (EA : forall v,code_relation M rho (CEvar 0) v -> v<>r)
    by (intros v HV;change (v=a) in HV;now subst v).
  assert (EB : forall v,code_relation M rho (CEvar 1) v -> v<>r)
    by (intros v HV;change (v=b) in HV;now subst v).
  assert (EK : forall v,code_relation M rho (CEvar 2) v -> v<>r)
    by (intros v HV;change (v=k) in HV;now subst v).
  assert (EP : forall v,code_relation M rho (CEvar 3) v -> v<>r)
    by (intros v HV;change (v=p) in HV;now subst v).
  assert (EM : expression_binder_absent M rho r (CEvar 4))
    by (intros v HV;change (v=m) in HV;now subst v).
  assert (EMP : expression_binder_absent M rho r (CEvar 5))
    by (intros v HV;change (v=mp) in HV;now subst v).
  unfold E_kp_conclusion. apply expression_binder_absent_existential;[exact EK|].
  apply expression_binder_absent_conjunction.
  - apply expression_binder_absent_universal;[exact EP|].
    apply expression_binder_absent_implication.
    + unfold E_kp_eligible. apply expression_binder_absent_disjunction.
      * apply expression_binder_absent_atom;now right.
      * apply expression_binder_absent_existential;[exact EB|].
        apply expression_binder_absent_conjunction.
        -- apply expression_binder_absent_atom;now left.
        -- unfold E_ksubset. apply expression_binder_absent_universal;[exact EK|].
           apply expression_binder_absent_implication;apply expression_binder_absent_atom;now left.
    + exact (request_binder_absent M rho (CEvar 1) (CEvar 2) (CEvar 5) b r eq_refl HBR EMP).
  - unfold E_kp_support_body. apply expression_binder_absent_universal;[exact EB|].
    apply expression_binder_absent_implication.
    + apply expression_binder_absent_atom;now left.
    + apply expression_binder_absent_existential;assumption.
Qed.

Theorem numerical_kp0_seed_specialization M a b k p m mp r f g allf result :
  a<>zeroM M -> a<>p -> b<>a -> k<>a -> a<>r ->
  b<>r -> k<>r -> p<>r ->
  named_binder_absent M m a -> named_binder_absent M m r ->
  named_substitution M m a p mp ->
  code_relation M (kp0_seed_parameters M a b k p m mp r)
    (E_kp_conclusion (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f ->
  code_relation M (kp0_seed_parameters M a b k p m mp r)
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) g ->
  universal_graph M a f allf -> implication_graph M allf g result ->
  numerically_provable M result.
Proof.
  intros H0 HAP HBA HKA HAR HBR HKR HPR HMA HMR HM HF HG HAll HResult.
  apply (numerical_stopping_specialization M f a r g allf result HAR).
  - apply (kp0_conclusion_binder_absent M a b k p m mp r f HAR HBR HKR HPR HMR);[|exact HF].
    exact (named_substitution_preserves_binders M m a p mp r HM HMR).
  - exact (kp0_seed_substitution M a b k p m mp r f g H0 HAP HBA HKA HAR
      HBR HKR HPR HMA HMR HM HF HG).
  - exact HAll.
  - exact HResult.
Qed.

Theorem numerical_kp0_with_seed M a b k p m mp r f g :
  a<>zeroM M -> a<>p -> b<>a -> k<>a -> a<>r ->
  b<>r -> k<>r -> p<>r ->
  named_binder_absent M m a -> named_binder_absent M m r ->
  named_substitution M m a p mp ->
  code_relation M (kp0_seed_parameters M a b k p m mp r)
    (E_kp_conclusion (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f ->
  code_relation M (kp0_seed_parameters M a b k p m mp r)
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) g ->
  numerically_provable M f -> numerically_provable M g.
Proof.
  intros H0 HAP HBA HKA HAR HBR HKR HPR HMA HMR HM HF HG PF.
  destruct (code_relation_total M (E_wal (CEvar 0) (CEvar 1))
    (arguments2 a f (zeroM M))) as [allf HAll].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allf g (zeroM M))) as [result HResult].
  apply (numerical_mp M allf g result).
  - exact (numerical_gen M a f allf PF HAll).
  - exact (numerical_kp0_seed_specialization M a b k p m mp r f g allf result
      H0 HAP HBA HKA HAR HBR HKR HPR HMA HMR HM HF HG HAll HResult).
  - exact HResult.
Qed.

Print Assumptions kp0_seed_substitution.
Print Assumptions kp0_conclusion_binder_absent.
Print Assumptions numerical_kp0_seed_specialization.
Print Assumptions numerical_kp0_with_seed.
