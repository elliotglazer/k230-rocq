(** A finite actual source-calculus selection-witness rule in an ordinary
    context. Eigenvariable vacuity is explicit for both the context and theta. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalEnvironments NumericalSourceFull SourceTraceBounds SourceContextProofHelpers
 SourceIffGraphs SourceConjunctionRules SourceDerivedRules SourceUpperProofHelpers SourceNamedVacuity
 SourceNamedSelfSpecialization SourceNamedElimination SourceNamedQuantifierRules.
Unset Implicit Arguments.
Theorem source_full_named_selection_equivalence M b c n z extension member theta equiv point all exExt pair sc result k:
 context_bounded M b c n k ->source_named_context_vacuous M b c n z ->
 source_bounded M extension k ->source_bounded M member k ->source_bounded M theta k ->
 source_named_vacuous M z theta ->source_iff_graph M member theta equiv ->
 sf_relation M SFImpl extension equiv point ->source_named_quantifier M true z point all ->
 source_named_quantifier M false z extension exExt ->sf_relation M SFAnd member extension pair ->
 source_named_quantifier M false z pair sc ->source_iff_graph M sc theta result ->
 source_full_prv M b c n all ->source_full_prv M b c n exExt ->source_full_prv M b c n result.
Proof.
 intros BC VC BE BM BT VT HI HP HA HE HPair HSC HResult PAll PEx.
 pose proof(source_iff_bounded M member theta equiv k BM BT HI)as BI.
 pose proof(proj2(source_bounded_accept_binary M SFImpl extension equiv point k
  (or_intror(or_intror eq_refl))HP)(conj BE BI))as BP.
 pose proof(proj2(source_bounded_accept_binary M SFAnd member extension pair k
  (or_introl eq_refl)HPair)(conj BM BE))as BPair.
 pose proof(source_named_quantifier_bound M false z pair sc k BPair HSC)as BSC.
 pose proof(source_named_quantifier_is_vacuous M false z pair sc k BPair HSC)as VSC.
 destruct(source_iff_parts M member theta equiv HI)as(mt&tm&HMT&HTM&HBoth).
 destruct(source_iff_parts M sc theta result HResult)as(forward&backward&HF&HR&HResultBoth).
 assert(PForward:source_full_prv M b c n forward).
 { destruct(environment_cons_total M b c n sc)as(u&v&l&HC).
   pose proof(proj2(context_bounded_cons M b c n sc u v l k HC)(conj BSC BC))as BC1.
   pose proof(source_full_cons_head M b c n sc u v l k HC BSC BC1)as PSC.
   destruct(environment_cons_total M u v l pair)as(d&e&m&HD).
   pose proof(proj2(context_bounded_cons M u v l pair d e m k HD)(conj BPair BC1))as BC2.
   pose proof(source_full_cons_head M u v l pair d e m k HD BPair BC2)as PPair.
   pose proof(source_full_conjunction_left M d e m member extension pair HPair PPair)as PM.
   pose proof(source_full_conjunction_right M d e m member extension pair HPair PPair)as PE.
   pose proof(source_full_cons_weaken M b c n sc u v l k all HC BC1 PAll)as PA1.
   pose proof(source_full_cons_weaken M u v l pair d e m k all HD BC2 PA1)as PA2.
   assert(PPoint:source_full_prv M d e m point).
   { destruct HA as(rb&rc&body&HM&HN&HAll).
     exact(source_full_named_self_all_elim M d e m point z rb rc body all k BP HM HN HAll PA2). }
   pose proof(source_full_modus_ponens M d e m extension equiv point HP PPoint PE)as PI.
   pose proof(source_full_modus_ponens M d e m member theta mt HMT
    (source_full_conjunction_left M d e m mt tm equiv HBoth PI)PM)as PT.
   destruct(sf_relation_total M SFImpl pair theta)as(local&HLocal).
   pose proof(source_full_implication_intro M u v l pair theta local d e m HD HLocal PT)as PLocal.
   pose proof(source_named_context_vacuous_cons M b c n sc u v l z HC VC VSC)as VC1.
   pose proof(source_full_named_exists_elim M u v l z pair sc theta local VC1 VT HSC HLocal PLocal PSC)as PTheta.
   exact(source_full_implication_intro M b c n sc theta forward u v l HC HF PTheta). }
 assert(PBackward:source_full_prv M b c n backward).
 { destruct(environment_cons_total M b c n theta)as(u&v&l&HC).
   pose proof(proj2(context_bounded_cons M b c n theta u v l k HC)(conj BT BC))as BC1.
   pose proof(source_full_cons_head M b c n theta u v l k HC BT BC1)as PTheta.
   destruct(environment_cons_total M u v l extension)as(d&e&m&HD).
   pose proof(proj2(context_bounded_cons M u v l extension d e m k HD)(conj BE BC1))as BC2.
   pose proof(source_full_cons_head M u v l extension d e m k HD BE BC2)as PE.
   pose proof(source_full_cons_weaken M b c n theta u v l k all HC BC1 PAll)as PA1.
   pose proof(source_full_cons_weaken M u v l extension d e m k all HD BC2 PA1)as PA2.
   assert(PPoint:source_full_prv M d e m point).
   { destruct HA as(rb&rc&body&HM&HN&HAll).
     exact(source_full_named_self_all_elim M d e m point z rb rc body all k BP HM HN HAll PA2). }
   pose proof(source_full_modus_ponens M d e m extension equiv point HP PPoint PE)as PI.
   pose proof(source_full_cons_weaken M u v l extension d e m k theta HD BC2 PTheta)as PT.
   pose proof(source_full_modus_ponens M d e m theta member tm HTM
    (source_full_conjunction_right M d e m mt tm equiv HBoth PI)PT)as PM.
   pose proof(source_full_conjunction M d e m member extension pair HPair PM PE)as PPair.
   pose proof(source_full_named_quantifier_ex_intro M d e m z pair sc HSC PPair)as PSC.
   destruct(sf_relation_total M SFImpl extension sc)as(local&HLocal).
   pose proof(source_full_implication_intro M u v l extension sc local d e m HD HLocal PSC)as PLocal.
   pose proof(source_full_cons_weaken M b c n theta u v l k exExt HC BC1 PEx)as PEx1.
   pose proof(source_named_context_vacuous_cons M b c n theta u v l z HC VC VT)as VC1.
   pose proof(source_full_named_exists_elim M u v l z extension exExt sc local VC1 VSC HE HLocal PLocal PEx1)as PSc.
   exact(source_full_implication_intro M b c n theta sc backward u v l HC HR PSc). }
 exact(source_full_conjunction M b c n forward backward result HResultBoth PForward PBackward).
Qed.
Print Assumptions source_full_named_selection_equivalence.
