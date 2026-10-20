(** Curry fixed universal propositional programs with actual source II/AllI.
    The finite template list is external; every formula hole may be internal. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceUniversalPrograms SourceFiniteTelescope NumericalContexts NumericalSourceFull.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_universal_template_graph M rho p all:=exists body,
 code_relation M rho(source_prop_expression p)body /\sf_relation M SFAll body(zeroM M)all.
Definition source_universal_macro_graph M rho A codes:=Forall2(source_universal_template_graph M rho)A codes.
Theorem source_universal_macro_total M rho A:exists codes,source_universal_macro_graph M rho A codes.
Proof.
 induction A as[|a A IH].
 - exists nil. constructor.
 - destruct IH as(codes&HC).
   destruct(code_relation_total M(source_prop_expression a)rho)as(body&HB).
   destruct(sf_relation_total M SFAll body(zeroM M))as(all&HA).
   exists(all::codes). constructor;[exists body;auto|exact HC].
Qed.
Lemma source_universal_macro_forward M rho A codes:
 source_universal_macro_graph M rho A codes ->forall p,In p A ->exists all,
 In all codes /\source_universal_template_graph M rho p all.
Proof.
 intro H. induction H;intros p HP;[contradiction|].
 destruct HP as[<-|HP].
 - exists y. split;[now left|exact H].
 - destruct(IHForall2 p HP)as(all&HA&HG). exists all. split;[now right|exact HG].
Qed.
Lemma source_universal_macro_backward M rho A codes:
 source_universal_macro_graph M rho A codes ->forall all,In all codes ->exists p,
 In p A /\source_universal_template_graph M rho p all.
Proof.
 intro H. induction H;intros all HA;[contradiction|].
 destruct HA as[<-|HA].
 - exists x. split;[now left|exact H].
 - destruct(IHForall2 all HA)as(p&HP&HG). exists p. split;[now right|exact HG].
Qed.
Theorem source_empty_universal_macro M rho k A p codes body all out:
 (forall i,source_bounded M(rho i)(succM M k)) ->source_prop_program A p ->
 source_universal_macro_graph M rho A codes ->
 code_relation M rho(source_prop_expression p)body ->sf_relation M SFAll body(zeroM M)all ->
 source_finite_telescope M codes all out ->source_full_prv M(zeroM M)(zeroM M)(zeroM M)out.
Proof.
 intros HB Program HG HBody HAll HTelescope.
 assert(BCodes:forall a,In a codes ->source_bounded M a k).
 { intros a HA. destruct(source_universal_macro_backward M rho A codes HG a HA)as(q&HQ&b&Hb&Hall).
   apply(proj2(source_bounded_accept_unary M SFAll b a k(or_introl eq_refl)Hall)).
   exact(source_prop_template_bound M rho q(succM M k)HB b Hb). }
 assert(BAll:source_bounded M all k).
 { apply(proj2(source_bounded_accept_unary M SFAll body all k(or_introl eq_refl)HAll)).
   exact(source_prop_template_bound M rho p(succM M k)HB body HBody). }
 apply(source_full_finite_telescope M codes all out k BCodes BAll HTelescope
  (zeroM M)(zeroM M)(zeroM M)(context_bounded_empty M _ _ k)).
 intros cb cc cn HC Included Premises.
 apply(source_full_universal_program M A p Program rho k cb cc cn body all HB HC);[|exact HBody|exact HAll].
 intros q HQ b aq Hb Haq.
 destruct(source_universal_macro_forward M rho A codes HG q HQ)as(a&HA&b'&Hb'&Ha').
 assert(E:b=b')by(eapply code_relation_functional;eassumption). subst b'.
 assert(E:aq=a)by(eapply sf_relation_functional;eassumption). subst a.
 exact(Premises aq HA).
Qed.
Print Assumptions source_universal_macro_total.
Print Assumptions source_universal_macro_forward.
Print Assumptions source_universal_macro_backward.
Print Assumptions source_empty_universal_macro.
