(** Harmless finite equality padding forces the KP0 names to avoid three
    fixed names even if those names disappeared during matrix substitution. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates ProofMacros QuantifierMacros NamedLeibnizSteps NumericalFixedSeed NumericalKP0
  NumericalKP0Requests NumericalKP0Eligibility KP0SeedSpecialization KP0MatrixTransport
  TemplateBinderFresh TemplateNamedSubstitution TemplateFormulaFresh
  NamedBinderFresh NamedSubstitution NamedSubstitutionFunctionality FreshNames
  ExpressionFreshElimination NumericalTaggedMatrix.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_collection_three_pad X Q D F :=
  E_wa (E_weq X X) (E_wa (E_weq Q Q) (E_wa (E_weq D D) F)).

Lemma collection_mentions_conjunction_right M rho y A B :
  expression_mentions M rho y B -> expression_mentions M rho y (E_wa A B).
Proof.
  unfold E_wa,E_wn. intro H.
  apply expression_mentions_implication_left,expression_mentions_implication_right,expression_mentions_implication_left,H.
Qed.

Lemma collection_three_pad_absent M rho y X Q D F :
  expression_binder_absent M rho y F ->
  expression_binder_absent M rho y (E_collection_three_pad X Q D F).
Proof.
  intro H. unfold E_collection_three_pad.
  repeat apply expression_binder_absent_conjunction;
    try (apply expression_binder_absent_atom;now right);assumption.
Qed.

Lemma collection_three_pad_fresh M rho y X Q D F :
  expression_fresh M rho y (E_collection_three_pad X Q D F) ->
  expression_name_avoids M rho y X /\ expression_name_avoids M rho y Q /\
  expression_name_avoids M rho y D /\ expression_fresh M rho y F.
Proof.
  unfold E_collection_three_pad. intro H.
  apply expression_fresh_conjunction_parts in H. destruct H as [HX H].
  apply expression_fresh_conjunction_parts in H. destruct H as [HQ H].
  apply expression_fresh_conjunction_parts in H. destruct H as [HD HF].
  apply expression_fresh_equality_names in HX,HQ,HD.
  destruct HX as [HX _]. destruct HQ as [HQ _]. destruct HD as [HD _]. auto.
Qed.

Lemma collection_three_pad_substitution M rho x p X Q D F Fp :
  x<>zeroM M ->
  expression_name_avoids M rho x X -> expression_name_avoids M rho x Q ->
  expression_name_avoids M rho x D ->
  expression_named_substitution M rho rho x p F Fp ->
  expression_named_substitution M rho rho x p
    (E_collection_three_pad X Q D F) (E_collection_three_pad X Q D Fp).
Proof.
  intros H0 HX HQ HD HS.
  assert (fixed:forall A,expression_name_avoids M rho x A ->
    expression_named_replace M rho rho x p A A).
  { intros A HA a b H1 H2. right. split;[exact (HA a H1)|].
    symmetry. exact (code_relation_functional M A rho a b H1 H2). }
  unfold E_collection_three_pad.
  repeat apply expression_ns_conjunction;try exact H0;try exact HS;
    apply (expression_ns_atom M rho rho x p true);apply fixed;assumption.
Qed.

Lemma numerical_collection_remove_three_pad M rho Seed A B K P X Q D F Fp :
  ns_proof M rho (E_wim
    (E_kp_with_seed Seed A B K P (E_collection_three_pad X Q D F)
      (E_collection_three_pad X Q D Fp))
    (E_kp_with_seed Seed A B K P F Fp)).
Proof.
  unfold E_collection_three_pad. apply (ns_proof_macro M rho
    (E_wim (E_kp_with_seed Seed A B K P
       (E_wa (E_weq X X) (E_wa (E_weq Q Q) (E_wa (E_weq D D) F)))
       (E_wa (E_weq X X) (E_wa (E_weq Q Q) (E_wa (E_weq D D) Fp))))
      (E_kp_with_seed Seed A B K P (E_wa (E_weq Q Q) (E_wa (E_weq D D) F))
        (E_wa (E_weq Q Q) (E_wa (E_weq D D) Fp))) ::
     E_wim (E_kp_with_seed Seed A B K P (E_wa (E_weq Q Q) (E_wa (E_weq D D) F))
        (E_wa (E_weq Q Q) (E_wa (E_weq D D) Fp)))
      (E_kp_with_seed Seed A B K P (E_wa (E_weq D D) F) (E_wa (E_weq D D) Fp)) ::
     E_wim (E_kp_with_seed Seed A B K P (E_wa (E_weq D D) F) (E_wa (E_weq D D) Fp))
      (E_kp_with_seed Seed A B K P F Fp) :: nil)).
  - intros e [<-|[<-|[<-|[]]]];apply numerical_kp0_remove_equality_padding.
  - eapply macro_syl;[apply PM_input;now left|].
    eapply macro_syl;apply PM_input;cbn;tauto.
Qed.

Theorem numerical_collection_avoiding_kp0 M i v root x q d m :
  i<>zeroM M -> v<>i -> i<>root -> v<>root ->
  x<>i -> q<>i -> d<>i ->
  named_binder_absent M m i -> named_binder_absent M m root -> formula_mentions M m root ->
  exists k p mp f,
    k<>i /\ k<>v /\ k<>root /\ i<>p /\ v<>p /\ k<>p /\ p<>root /\ p<>zeroM M /\
    k<>x /\ k<>q /\ k<>d /\ p<>x /\ p<>q /\ p<>d /\
    formula_fresh M m k /\ formula_fresh M m p /\ named_substitution M m i p mp /\
    code_relation M (kp0_seed_parameters M i v k p m mp root)
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f /\
    numerically_provable M f.
Proof.
  intros H0 HVI HIR HVR HXI HQI HDI HMI HMR Hmention.
  set (r0:=x .: q .: d .: m .: fun _=>zeroM M).
  set (Pad:=E_collection_three_pad (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)).
  destruct (code_relation_total M Pad r0) as [pad Hpad].
  assert (HAI:named_binder_absent M pad i).
  { exact (collection_three_pad_absent M r0 i (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
      ltac:(intros f Hf;change (f=m) in Hf;now subst f) pad Hpad). }
  assert (HAR:named_binder_absent M pad root).
  { exact (collection_three_pad_absent M r0 root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
      ltac:(intros f Hf;change (f=m) in Hf;now subst f) pad Hpad). }
  assert (HPmention:formula_mentions M pad root).
  { assert (HH:expression_mentions M r0 root Pad).
    { unfold Pad,E_collection_three_pad.
      do 3 apply collection_mentions_conjunction_right.
      intros f Hf. change (f=m) in Hf. now subst f. }
    exact (HH pad Hpad). }
  destruct (numerical_uniform_kp0_fixed_seed M i v pad root H0 HVI HIR HVR HAI HAR HPmention)
    as (k&p&padp&old&HKI&HKV&HKR&HIP&HVP&HKP&HPR&HP0&HKfresh&HPfresh&HSub&HOld&POld).
  assert (HK:expression_fresh M r0 k Pad).
  { intros f Hf. rewrite (code_relation_functional M Pad r0 f pad Hf Hpad). exact HKfresh. }
  assert (HP:expression_fresh M r0 p Pad).
  { intros f Hf. rewrite (code_relation_functional M Pad r0 f pad Hf Hpad). exact HPfresh. }
  destruct (collection_three_pad_fresh M r0 k (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) HK)
    as [HKX [HKQ [HKD HKM]]].
  destruct (collection_three_pad_fresh M r0 p (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) HP)
    as [HPX [HPQ [HPD HPM]]].
  assert (FMK:formula_fresh M m k) by exact (HKM m eq_refl).
  assert (FMP:formula_fresh M m p) by exact (HPM m eq_refl).
  destruct (named_substitution_fresh_total M m i p FMP) as [mp HS].
  set (rho:=i .: v .: k .: p .: m .: mp .: root .: x .: q .: d .: fun _=>zeroM M).
  set (Padded:=E_collection_three_pad (CEvar 7) (CEvar 8) (CEvar 9) (CEvar 4)).
  set (PaddedP:=E_collection_three_pad (CEvar 7) (CEvar 8) (CEvar 9) (CEvar 5)).
  assert (HPad:code_relation M rho Padded pad) by exact Hpad.
  destruct (code_relation_total M PaddedP rho) as [padp' HPadP].
  assert (HSP:named_substitution M pad i p padp').
  { apply (collection_three_pad_substitution M rho i p (CEvar 7) (CEvar 8) (CEvar 9) (CEvar 4) (CEvar 5)
      H0 ltac:(intros f Hf;change (f=x) in Hf;congruence)
      ltac:(intros f Hf;change (f=q) in Hf;congruence)
      ltac:(intros f Hf;change (f=d) in Hf;congruence)).
    - intros f g Hf Hg. change (f=m) in Hf. change (g=mp) in Hg. now subst f g.
    - exact HPad.
    - exact HPadP. }
  assert (E:padp=padp') by exact (named_substitution_functional M pad i p padp padp' HSub HSP).
  subst padp'.
  set (repl:=CEvar 0 .: CEvar 1 .: CEvar 2 .: CEvar 3 .: Padded .: PaddedP .: CEvar 6 .: fun _=>CEconst 0).
  assert (HOld':code_relation M rho
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) Padded PaddedP) old).
  { assert (HR:forall j,code_relation M rho (repl j) (kp0_seed_parameters M i v k p pad padp root j)).
    { intros [|[|[|[|[|[|[|j]]]]]]];try reflexivity;assumption. }
    exact (proj2 (code_subst_graph M rho repl (kp0_seed_parameters M i v k p pad padp root) HR
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) old) HOld). }
  assert (PBefore:ns_proof M rho
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) Padded PaddedP)).
  { intros f Hf. rewrite (code_relation_functional M _ rho f old Hf HOld'). exact POld. }
  assert (PAfter:ns_proof M rho
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5))).
  { eapply ns_proof_mp;[exact PBefore|apply numerical_collection_remove_three_pad]. }
  destruct (code_relation_total M
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) rho) as [f Hf].
  assert (HKX':k<>x) by (intro E;apply (HKX x eq_refl);symmetry;exact E).
  assert (HKQ':k<>q) by (intro E;apply (HKQ q eq_refl);symmetry;exact E).
  assert (HKD':k<>d) by (intro E;apply (HKD d eq_refl);symmetry;exact E).
  assert (HPX':p<>x) by (intro E;apply (HPX x eq_refl);symmetry;exact E).
  assert (HPQ':p<>q) by (intro E;apply (HPQ q eq_refl);symmetry;exact E).
  assert (HPD':p<>d) by (intro E;apply (HPD d eq_refl);symmetry;exact E).
  exists k,p,mp,f. repeat split;try assumption.
  exact (PAfter f Hf).
Qed.

Print Assumptions collection_three_pad_substitution.
Print Assumptions numerical_collection_remove_three_pad.
Print Assumptions numerical_collection_avoiding_kp0.






