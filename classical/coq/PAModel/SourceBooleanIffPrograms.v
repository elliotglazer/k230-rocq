(** Finite direct proof programs for congruence of all source booleans. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SourceBounded
  NumericalContexts NumericalSourceFull SourceIffGraphs SourcePropositionalTemplates SourceRelativizationRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition tv_iff_template a b:=SPTAnd(SPTImpl a b)(SPTImpl b a).
Definition tv_binary_template h a b:=match h with SFAnd=>SPTAnd a b|SFOr=>SPTOr a b|_=>SPTImpl a b end.
Definition tv_boolean_hypotheses:=cons(tv_iff_template(SPTSlot 0)(SPTSlot 2))
  (cons(tv_iff_template(SPTSlot 1)(SPTSlot 3))nil).
Ltac tv_boolean_ctx:=apply SPTCtx;cbn;auto 12.
Lemma tv_and_iff_program:source_prop_program tv_boolean_hypotheses
  (tv_iff_template(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTAnd(SPTSlot 2)(SPTSlot 3))).
Proof.
  unfold tv_boolean_hypotheses,tv_iff_template. apply SPTCI.
  - apply SPTII,SPTCI.
    + eapply(SPTIE _(SPTSlot 0));[apply(SPTCE1 _ _(SPTImpl(SPTSlot 2)(SPTSlot 0)));tv_boolean_ctx|].
      apply(SPTCE1 _ _(SPTSlot 1));tv_boolean_ctx.
    + eapply(SPTIE _(SPTSlot 1));[apply(SPTCE1 _ _(SPTImpl(SPTSlot 3)(SPTSlot 1)));tv_boolean_ctx|].
      apply(SPTCE2 _(SPTSlot 0));tv_boolean_ctx.
  - apply SPTII,SPTCI.
    + eapply(SPTIE _(SPTSlot 2));[apply(SPTCE2 _(SPTImpl(SPTSlot 0)(SPTSlot 2)));tv_boolean_ctx|].
      apply(SPTCE1 _ _(SPTSlot 3));tv_boolean_ctx.
    + eapply(SPTIE _(SPTSlot 3));[apply(SPTCE2 _(SPTImpl(SPTSlot 1)(SPTSlot 3)));tv_boolean_ctx|].
      apply(SPTCE2 _(SPTSlot 2));tv_boolean_ctx.
Qed.
Lemma tv_or_iff_program:source_prop_program tv_boolean_hypotheses
  (tv_iff_template(SPTOr(SPTSlot 0)(SPTSlot 1))(SPTOr(SPTSlot 2)(SPTSlot 3))).
Proof.
  unfold tv_boolean_hypotheses,tv_iff_template. apply SPTCI.
  - apply SPTII. eapply(SPTDE _(SPTSlot 0)(SPTSlot 1));[tv_boolean_ctx| |].
    + apply SPTDI1. eapply(SPTIE _(SPTSlot 0));[apply(SPTCE1 _ _(SPTImpl(SPTSlot 2)(SPTSlot 0)));tv_boolean_ctx|tv_boolean_ctx].
    + apply SPTDI2. eapply(SPTIE _(SPTSlot 1));[apply(SPTCE1 _ _(SPTImpl(SPTSlot 3)(SPTSlot 1)));tv_boolean_ctx|tv_boolean_ctx].
  - apply SPTII. eapply(SPTDE _(SPTSlot 2)(SPTSlot 3));[tv_boolean_ctx| |].
    + apply SPTDI1. eapply(SPTIE _(SPTSlot 2));[apply(SPTCE2 _(SPTImpl(SPTSlot 0)(SPTSlot 2)));tv_boolean_ctx|tv_boolean_ctx].
    + apply SPTDI2. eapply(SPTIE _(SPTSlot 3));[apply(SPTCE2 _(SPTImpl(SPTSlot 1)(SPTSlot 3)));tv_boolean_ctx|tv_boolean_ctx].
Qed.
Lemma tv_imp_iff_program:source_prop_program tv_boolean_hypotheses
  (tv_iff_template(SPTImpl(SPTSlot 0)(SPTSlot 1))(SPTImpl(SPTSlot 2)(SPTSlot 3))).
Proof.
  unfold tv_boolean_hypotheses,tv_iff_template. apply SPTCI.
  - do 2 apply SPTII. eapply(SPTIE _(SPTSlot 1));[apply(SPTCE1 _ _(SPTImpl(SPTSlot 3)(SPTSlot 1)));tv_boolean_ctx|].
    eapply(SPTIE _(SPTSlot 0));[tv_boolean_ctx|].
    eapply(SPTIE _(SPTSlot 2));[apply(SPTCE2 _(SPTImpl(SPTSlot 0)(SPTSlot 2)));tv_boolean_ctx|tv_boolean_ctx].
  - do 2 apply SPTII. eapply(SPTIE _(SPTSlot 3));[apply(SPTCE2 _(SPTImpl(SPTSlot 1)(SPTSlot 3)));tv_boolean_ctx|].
    eapply(SPTIE _(SPTSlot 2));[tv_boolean_ctx|].
    eapply(SPTIE _(SPTSlot 0));[apply(SPTCE1 _ _(SPTImpl(SPTSlot 2)(SPTSlot 0)));tv_boolean_ctx|tv_boolean_ctx].
Qed.
Lemma tv_binary_iff_program h:sf_binary h ->source_prop_program tv_boolean_hypotheses
  (tv_iff_template(tv_binary_template h(SPTSlot 0)(SPTSlot 1))(tv_binary_template h(SPTSlot 2)(SPTSlot 3))).
Proof. intros [H|[H|H]];subst h;[apply tv_and_iff_program|apply tv_or_iff_program|apply tv_imp_iff_program]. Qed.
Lemma source_tv_iff_template_graph M rho A B a b out:
  code_relation M rho(source_prop_expression A)a ->code_relation M rho(source_prop_expression B)b ->
  source_iff_graph M a b out ->code_relation M rho(source_prop_expression(tv_iff_template A B))out.
Proof.
  intros GA GB HI. destruct(source_iff_parts M a b out HI)as(lr&rl&HL&HR&HO).
  eapply(source_prop_template_join M rho SFAnd(SPTImpl A B)(SPTImpl B A)lr rl out).
  - exact(source_prop_template_join M rho SFImpl A B a b lr GA GB HL).
  - exact(source_prop_template_join M rho SFImpl B A b a rl GB GA HR).
  - exact HO.
Qed.
Lemma source_tv_binary_template_graph M rho h A B a b out:
  sf_binary h ->code_relation M rho(source_prop_expression A)a ->code_relation M rho(source_prop_expression B)b ->
  sf_relation M h a b out ->code_relation M rho(source_prop_expression(tv_binary_template h A B))out.
Proof.
  intros [H|[H|H]] GA GB HO;subst h;cbn[tv_binary_template];eapply source_prop_template_join;eassumption.
Qed.
Definition tv_boolean_values M a b c d i:=match i with 0=>a|1=>b|2=>c|3=>d|_=>zeroM M end.
Theorem source_full_iff_binary M cb cc cn h a b c d left right ac bd equiv k:
  sf_binary h ->context_bounded M cb cc cn k ->source_bounded M a k ->source_bounded M b k ->
  source_bounded M c k ->source_bounded M d k ->sf_relation M h a b left ->sf_relation M h c d right ->
  source_iff_graph M a c ac ->source_iff_graph M b d bd ->source_iff_graph M left right equiv ->
  source_full_prv M cb cc cn ac ->source_full_prv M cb cc cn bd ->source_full_prv M cb cc cn equiv.
Proof.
  intros HH BC BA BB BCC BD HL HR HAC HBD HE PAC PBD.
  set(rho:=tv_boolean_values M a b c d).
  assert(BValues:forall i,source_bounded M(rho i)k).
  { intros[|[|[|[|i]]]];cbn[rho tv_boolean_values];try assumption;apply source_bounded_accept_falsity. }
  assert(GAC:code_relation M rho(source_prop_expression(tv_iff_template(SPTSlot 0)(SPTSlot 2)))ac).
  { exact(source_tv_iff_template_graph M rho(SPTSlot 0)(SPTSlot 2)a c ac eq_refl eq_refl HAC). }
  assert(GBD:code_relation M rho(source_prop_expression(tv_iff_template(SPTSlot 1)(SPTSlot 3)))bd).
  { exact(source_tv_iff_template_graph M rho(SPTSlot 1)(SPTSlot 3)b d bd eq_refl eq_refl HBD). }
  apply(source_prop_program_sound M _ _(tv_binary_iff_program h HH)rho k cb cc cn equiv BValues BC).
  - intros p[<-|[<-|[]]]f HF.
    + rewrite(code_relation_functional M _ rho f ac HF GAC). exact PAC.
    + rewrite(code_relation_functional M _ rho f bd HF GBD). exact PBD.
  - apply(source_tv_iff_template_graph M rho(tv_binary_template h(SPTSlot 0)(SPTSlot 1))
      (tv_binary_template h(SPTSlot 2)(SPTSlot 3))left right equiv);[| |exact HE].
    + exact(source_tv_binary_template_graph M rho h(SPTSlot 0)(SPTSlot 1)a b left HH eq_refl eq_refl HL).
    + exact(source_tv_binary_template_graph M rho h(SPTSlot 2)(SPTSlot 3)c d right HH eq_refl eq_refl HR).
Qed.
Print Assumptions tv_and_iff_program.
Print Assumptions tv_or_iff_program.
Print Assumptions tv_imp_iff_program.
Print Assumptions source_full_iff_binary.
