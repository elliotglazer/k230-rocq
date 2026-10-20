(** The first raw-theory steps from the numerical K core toward KP0.
    These results supply its output-root formula and support half for an
    arbitrary internal matrix. Seed conversion below exposes the exact
    remaining bound-variable vacuity interface, rather than assuming that
    semantic vacuity is the stronger formula_fresh predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofClosure ProofTemplates TemplateCD TemplatePropositional ProofMacros
  QuantifierMacros NumericalVacuitySteps NumericalBootstrap
  NumericalCoreCongruence FreshNames NamedExistential NamedLeibnizSteps
  NamedSelfExistential NamedAlpha NamedBinderConstructors NamedSpecialization
  TemplateBinderFresh NumericalVacuity NamedBinderFresh BoundVariableVacuityRules
  StoppingSpecialization.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition E_kp_emitted a b k m :=
  E_wal b (E_wim (E_wel b k)
    (E_wex a (E_wa m (E_wal a
      (E_wim (E_ksubset a b k) (E_krequest b k m)))))).

Definition E_kp_output_root a b k m :=
  E_wal b (E_wex k (E_wa (E_wim m (E_wel b k))
    (E_kp_emitted a b k m))).

Definition E_kp_seed_root a b k m :=
  E_wex k (E_wa
    (E_wim (E_wex b m) (E_wex b (E_wa (E_wel b k) m)))
    (E_kp_emitted a b k m)).

Definition E_kp_support a b k m :=
  E_wex k (E_wal b (E_wim (E_wel b k) (E_wex a m))).

Lemma kp0_implication_map G inputs p q r :
  proof_macro G inputs (E_wim q r) ->
  proof_macro G inputs (E_wim (E_wim p q) (E_wim p r)).
Proof.
  intro H. apply macro_discharge. do 2 apply macro_deduction.
  eapply md_mp with (a:=q).
  - eapply md_mp with (a:=p);apply md_hyp;cbn;tauto.
  - apply md_global;exact H.
Qed.

Lemma kp0_core_support_program a b k m :
  proof_macro nil (E_kcore a b k m :: nil) (E_kp_support a b k m).
Proof.
  eapply PM_mp;[apply PM_input;now left|].
  unfold E_kcore,E_kp_support. apply macro_exists_monotone.
  eapply macro_syl;[apply PM_template,bootstrap_projection_right|].
  apply macro_all_monotone,kp0_implication_map,macro_exists_monotone.
  apply PM_template,bootstrap_projection_left.
Qed.

Theorem numerical_kcore_support M a b k m f support :
  code_relation M (code_parameters a b k m)
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) f ->
  code_relation M (code_parameters a b k m)
    (E_kp_support (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) support ->
  numerically_provable M f -> numerically_provable M support.
Proof.
  intros HF HS HP. apply (unguarded_macro_sound M (code_parameters a b k m)
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) :: nil)
    (E_kp_support (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))).
  - intros e [<-|[]] v HV.
    assert (v=f) by exact (code_relation_functional M _ _ v f HV HF).
    now subst v.
  - apply kp0_core_support_program.
  - exact HS.
Qed.

Theorem numerical_kp0_output_and_support M a b m :
  exists k root support,
    k<>a /\ k<>b /\ formula_fresh M m k /\
    code_relation M (code_parameters a b k m)
      (E_kp_output_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) root /\
    numerically_provable M root /\
    code_relation M (code_parameters a b k m)
      (E_kp_support (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) support /\
    numerically_provable M support.
Proof.
  destruct (numerical_uniform_kcore M a b m) as [k [core [Hka [Hkb [Hfresh [HC PC]]]]]].
  set (env:=code_parameters a b k m).
  destruct (code_relation_total M
    (E_kp_output_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) env) as [root HR].
  destruct (code_relation_total M
    (E_kp_support (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) env) as [support HS].
  assert (P_root:numerically_provable M root).
  { apply (numerical_gen M b core root PC).
    exact (expression_universal_graph M env (CEvar 1)
      (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) b core root eq_refl HC HR). }
  exists k,root,support. split;[exact Hka|]. split;[exact Hkb|].
  split;[exact Hfresh|]. split;[exact HR|]. split;[exact P_root|]. split;[exact HS|].
  exact (numerical_kcore_support M a b k m core support HC HS PC).
Qed.

Lemma kp0_conjunction G p q :
  template_proof G (E_wim p (E_wim q (E_wa p q))).
Proof.
  apply template_discharge. do 2 apply template_deduction.
  apply template_der_andi;apply dhyp;cbn;tauto.
Qed.

Lemma kp0_md_conjunction G inputs delta p q :
  macro_derivation G inputs delta p -> macro_derivation G inputs delta q ->
  macro_derivation G inputs delta (E_wa p q).
Proof.
  intros HP HQ. eapply md_mp;[exact HQ|].
  eapply md_mp;[exact HP|]. apply md_global,PM_template,kp0_conjunction.
Qed.

(** Conditional monotonicity keeps its parameter outside the quantified
    formula only after consuming an actual proof of its vacuity. *)
Lemma kp0_parameter_exists inputs x p f g :
  proof_macro nil inputs (E_vac x p) ->
  proof_macro nil inputs (E_wim p (E_wim f g)) ->
  proof_macro nil inputs (E_wim p (E_wim (E_wex x f) (E_wex x g))).
Proof.
  intros HV HI. eapply macro_syl.
  - eapply macro_syl;[exact HV|apply macro_all_monotone;exact HI].
  - apply ns_macro_all_exists.
Qed.

Lemma kp0_exists_eliminate inputs x f g :
  proof_macro nil inputs (E_vac x g) ->
  proof_macro nil inputs (E_wim f g) ->
  proof_macro nil inputs (E_wim (E_wex x f) g).
Proof.
  intros HV HI. eapply macro_syl.
  - apply macro_exists_monotone;exact HI.
  - eapply macro_syl;[apply macro_exists_monotone;exact HV|].
    apply PM_template,template_r6.
Qed.

Definition E_seed_body x m e h :=
  E_wa (E_wim (E_wex x m) (E_wex x (E_wa e m))) h.
Definition E_seed_result x y m e h := E_wex y (E_seed_body x m e h).
Definition E_seed_core y m e h := E_wex y (E_wa (E_wim m e) h).

(** This finite program uses only four already-proved inputs: the core;
    introduction of the output witness; vacuity of the container name in
    the matrix; and vacuity of the output name in the closed seed. *)
Definition seed_conversion_inputs x y m e h :=
  E_seed_core y m e h ::
  E_wim (E_wa e m) (E_wex x (E_wa e m)) ::
  E_vac y m :: E_vac x (E_seed_result x y m e h) :: nil.

Lemma seed_conversion_program x y m e h :
  proof_macro nil (seed_conversion_inputs x y m e h)
    (E_seed_result x y m e h).
Proof.
  set (inputs:=seed_conversion_inputs x y m e h).
  set (f:=E_wa (E_wim m e) h).
  set (b:=E_seed_body x m e h).
  set (s:=E_seed_result x y m e h).
  set (p:=E_wex x m).
  assert (HPos : proof_macro nil inputs (E_wim m (E_wim f b))).
  { apply macro_discharge. do 2 apply macro_deduction.
    unfold b,E_seed_body. apply kp0_md_conjunction.
    - eapply md_mp with (a:=E_wex x (E_wa e m)).
      + eapply md_mp with (a:=E_wa e m).
        * apply kp0_md_conjunction.
          -- eapply md_mp with (a:=m);[apply md_hyp;cbn;tauto|].
             eapply md_mp with (a:=f);[apply md_hyp;cbn;tauto|].
             apply md_global,PM_template,bootstrap_projection_left.
          -- apply md_hyp;cbn;tauto.
        * apply md_global,PM_input;unfold inputs,seed_conversion_inputs;cbn;tauto.
      + apply md_global,PM_template,template_K.
    - eapply md_mp with (a:=f);[apply md_hyp;cbn;tauto|].
      apply md_global,PM_template,bootstrap_projection_right. }
  assert (HNeg : proof_macro nil inputs (E_wim (E_wn p) (E_wim f b))).
  { apply macro_discharge. do 2 apply macro_deduction.
    unfold b,E_seed_body. apply kp0_md_conjunction.
    - eapply md_mp with (a:=E_wn p);[apply md_hyp;cbn;tauto|].
      apply md_global,PM_template,template_negative_implication.
    - eapply md_mp with (a:=f);[apply md_hyp;cbn;tauto|].
      apply md_global,PM_template,bootstrap_projection_right. }
  assert (HVM : proof_macro nil inputs (E_vac y m)).
  { apply PM_input;unfold inputs,seed_conversion_inputs;cbn;tauto. }
  assert (HVNeg : proof_macro nil inputs (E_vac y (E_wn p))).
  { unfold p,E_wex. apply macro_vacuous_negation,macro_vacuous_negation.
    apply macro_vacuous_universal,macro_vacuous_negation. exact HVM. }
  assert (HP : proof_macro nil inputs (E_wim m s)).
  { pose proof (kp0_parameter_exists inputs y m f b HVM HPos) as HM.
    apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_wex y f).
    - apply md_global,PM_input;unfold inputs,seed_conversion_inputs,E_seed_core,f;cbn;tauto.
    - eapply md_mp with (a:=m);[apply md_hyp;cbn;tauto|].
      apply md_global;exact HM. }
  assert (HN : proof_macro nil inputs (E_wim (E_wn p) s)).
  { pose proof (kp0_parameter_exists inputs y (E_wn p) f b HVNeg HNeg) as HM.
    apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_wex y f).
    - apply md_global,PM_input;unfold inputs,seed_conversion_inputs,E_seed_core,f;cbn;tauto.
    - eapply md_mp with (a:=E_wn p);[apply md_hyp;cbn;tauto|].
      apply md_global;exact HM. }
  assert (HPS : proof_macro nil inputs (E_wim p s)).
  { apply kp0_exists_eliminate;[|exact HP].
    apply PM_input;unfold inputs,seed_conversion_inputs,s;cbn;tauto. }
  apply (PM_mp (E_wn (E_wn s))).
  - apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=s);[|apply md_hyp;cbn;tauto].
    eapply md_mp with (a:=E_wn p).
    + eapply md_mp with (a:=E_wn s);[apply md_hyp;cbn;tauto|].
      apply md_global,macro_contra;exact HPS.
    + apply md_global;exact HN.
  - apply PM_template,template_DNE.
Qed.

Theorem numerical_kp0_seed_from_interfaces M env a b k m seed :
  ns_proof M env (E_kcore a b k m) ->
  ns_proof M env (E_wim (E_wa (E_wel b k) m)
    (E_wex b (E_wa (E_wel b k) m))) ->
  ns_proof M env (E_vac k m) ->
  ns_proof M env (E_vac b (E_kp_seed_root a b k m)) ->
  code_relation M env (E_kp_seed_root a b k m) seed ->
  numerically_provable M seed.
Proof.
  intros HC HI HV HS HCode.
  apply (ns_proof_macro M env
    (seed_conversion_inputs b k m (E_wel b k) (E_kp_emitted a b k m))
    (E_seed_result b k m (E_wel b k) (E_kp_emitted a b k m))).
  - intros e [<-|[<-|[<-|[<-|[]]]]];assumption.
  - apply seed_conversion_program.
  - exact HCode.
Qed.

Theorem numerical_kp0_output_intro M env x y m xv :
  code_relation M env x xv -> expression_binder_absent M env xv m ->
  ns_proof M env (E_wim (E_wa (E_wel x y) m)
    (E_wex x (E_wa (E_wel x y) m))).
Proof.
  intros HX HM result HResult.
  destruct (code_relation_total M (E_wa (E_wel x y) m) env) as [body HB].
  destruct (code_relation_total M (E_wex x (E_wa (E_wel x y) m)) env) as [exbody HE].
  assert (HAbsent : named_binder_absent M body xv).
  { apply (expression_binder_absent_conjunction M env xv (E_wel x y) m).
    - apply expression_binder_absent_atom. now left.
    - exact HM.
    - exact HB. }
  apply (numerical_named_self_exists_intro M body xv exbody result HAbsent).
  - exact (proj1 (named_exists_expression M env x (E_wa (E_wel x y) m)
      xv body exbody HX HB) HE).
  - exact (proj1 (expression_implication_iff M env
      (E_wa (E_wel x y) m) (E_wex x (E_wa (E_wel x y) m))
      body exbody result HB HE) HResult).
Qed.

Theorem numerical_kcore_seed M a b k m core seed :
  code_relation M (code_parameters a b k m)
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) core ->
  numerically_provable M core -> named_binder_absent M m b -> formula_fresh M m k ->
  ns_proof M (code_parameters a b k m)
    (E_vac (CEvar 1) (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))) ->
  code_relation M (code_parameters a b k m)
    (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) seed ->
  numerically_provable M seed.
Proof.
  intros HC PC HM HK HV HS.
  apply (numerical_kp0_seed_from_interfaces M (code_parameters a b k m)
    (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) seed).
  - intros v Hv. assert (v=core) by exact (code_relation_functional M _ _ v core Hv HC).
    now subst v.
  - apply (numerical_kp0_output_intro M (code_parameters a b k m)
      (CEvar 1) (CEvar 2) (CEvar 3) b eq_refl).
    intros v Hv. change (v=m) in Hv. now subst v.
  - intros v Hv. apply (numerical_vacuity M k m v HK).
    exact (proj1 (expression_vacuity_graph M (code_parameters a b k m)
      (CEvar 2) (CEvar 3) k m v eq_refl eq_refl) Hv).
  - exact HV.
  - exact HS.
Qed.

Lemma kp0_vacuous_exists G inputs x y f :
  proof_macro G inputs (E_vac y f) ->
  proof_macro G inputs (E_vac y (E_wex x f)).
Proof.
  intro H. unfold E_wex. apply macro_vacuous_negation.
  apply macro_vacuous_universal,macro_vacuous_negation. exact H.
Qed.

Lemma kp0_vacuous_conjunction G inputs x f g :
  proof_macro G inputs (E_vac x f) ->
  proof_macro G inputs (E_vac x g) ->
  proof_macro G inputs (E_vac x (E_wa f g)).
Proof.
  intros HF HG. unfold E_wa. apply macro_vacuous_negation.
  apply macro_vacuous_implication;[exact HF|].
  apply macro_vacuous_negation. exact HG.
Qed.

(** The sole remaining seed-vacuity interface reduces to the standard
    bound-name rule for its three quantified pieces. *)
Lemma seed_bound_vacuity_program x y m e h :
  proof_macro nil
    (E_vac x (E_wex x m) :: E_vac x (E_wex x (E_wa e m)) :: E_vac x h :: nil)
    (E_vac x (E_seed_result x y m e h)).
Proof.
  unfold E_seed_result,E_seed_body. apply kp0_vacuous_exists,kp0_vacuous_conjunction.
  - apply macro_vacuous_implication;apply PM_input;cbn;tauto.
  - apply PM_input;cbn;tauto.
Qed.

Theorem numerical_kp0_seed_vacuity M env a b k m :
  ns_proof M env (E_vac b (E_kp_seed_root a b k m)).
Proof.
  apply (ns_proof_macro M env
    (E_vac b (E_wex b m) :: E_vac b (E_wex b (E_wa (E_wel b k) m)) ::
     E_vac b (E_kp_emitted a b k m) :: nil)).
  - intros p [<-|[<-|[<-|[]]]].
    + apply ns_bound_existential_vacuity.
    + apply ns_bound_existential_vacuity.
    + unfold E_kp_emitted. apply ns_bound_universal_vacuity.
  - apply seed_bound_vacuity_program.
Qed.

Theorem numerical_kcore_seed_direct M a b k m core seed :
  code_relation M (code_parameters a b k m)
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) core ->
  numerically_provable M core -> named_binder_absent M m b -> formula_fresh M m k ->
  code_relation M (code_parameters a b k m)
    (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) seed ->
  numerically_provable M seed.
Proof.
  intros HC PC HM HK HS.
  exact (numerical_kcore_seed M a b k m core seed HC PC HM HK
    (numerical_kp0_seed_vacuity M (code_parameters a b k m)
      (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) HS).
Qed.

Theorem numerical_uniform_kp0_seed M a b m :
  named_binder_absent M m b ->
  exists k seed, k<>a /\ k<>b /\ formula_fresh M m k /\
    code_relation M (code_parameters a b k m)
      (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) seed /\
    numerically_provable M seed.
Proof.
  intro HM.
  destruct (numerical_uniform_kcore M a b m) as [k [core [Hka [Hkb [HK [HC PC]]]]]].
  destruct (code_relation_total M
    (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))
    (code_parameters a b k m)) as [seed HS].
  exists k,seed. split;[exact Hka|]. split;[exact Hkb|]. split;[exact HK|].
  split;[exact HS|]. exact (numerical_kcore_seed_direct M a b k m core seed HC PC HM HK HS).
Qed.

Theorem numerical_kcore_seed_unrestricted M a b k m core seed :
  code_relation M (code_parameters a b k m)
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) core ->
  numerically_provable M core -> formula_fresh M m k ->
  code_relation M (code_parameters a b k m)
    (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) seed ->
  numerically_provable M seed.
Proof.
  intros HC PC HK HS.
  apply (numerical_kp0_seed_from_interfaces M (code_parameters a b k m)
    (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) seed).
  - intros v Hv. assert (v=core) by exact (code_relation_functional M _ _ v core Hv HC).
    now subst v.
  - apply ns_stopping_self_existential.
  - intros v Hv. apply (numerical_vacuity M k m v HK).
    exact (proj1 (expression_vacuity_graph M (code_parameters a b k m)
      (CEvar 2) (CEvar 3) k m v eq_refl eq_refl) Hv).
  - apply numerical_kp0_seed_vacuity.
  - exact HS.
Qed.

Theorem numerical_uniform_kp0_seed_unrestricted M a b m :
  exists k seed, k<>a /\ k<>b /\ formula_fresh M m k /\
    code_relation M (code_parameters a b k m)
      (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) seed /\
    numerically_provable M seed.
Proof.
  destruct (numerical_uniform_kcore M a b m) as [k [core [Hka [Hkb [HK [HC PC]]]]]].
  destruct (code_relation_total M
    (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))
    (code_parameters a b k m)) as [seed HS].
  exists k,seed. split;[exact Hka|]. split;[exact Hkb|]. split;[exact HK|].
  split;[exact HS|]. exact (numerical_kcore_seed_unrestricted M a b k m core seed HC PC HK HS).
Qed.

Print Assumptions kp0_core_support_program.
Print Assumptions numerical_kcore_support.
Print Assumptions numerical_kp0_output_and_support.
Print Assumptions seed_conversion_program.
Print Assumptions numerical_kp0_seed_from_interfaces.
Print Assumptions numerical_kp0_output_intro.
Print Assumptions numerical_kcore_seed.
Print Assumptions seed_bound_vacuity_program.
Print Assumptions numerical_kcore_seed_direct.
Print Assumptions numerical_uniform_kp0_seed.
Print Assumptions numerical_kcore_seed_unrestricted.
Print Assumptions numerical_uniform_kp0_seed_unrestricted.
