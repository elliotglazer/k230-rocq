(** Actual existential distribution for arbitrary numerical source matrices. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull SourceTraceBounds
  SourceUniversalDistribution SourceUniversalPropositional SourceNamedProofRules SourceContextProofHelpers
  SourceContextTransport SourceExistentialMap SourceLeastOrdinalWitness.
Unset Implicit Arguments.

Theorem source_existential_distribution M a b point exa exb qpoint inside out k:
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  sf_relation M SFImpl a b point ->sf_relation M SFEx a(zeroM M)exa ->
  sf_relation M SFEx b(zeroM M)exb ->sf_relation M SFAll point(zeroM M)qpoint ->
  sf_relation M SFImpl exa exb inside ->sf_relation M SFImpl qpoint inside out ->
  source_full_prv M(zeroM M)(zeroM M)(zeroM M)out.
Proof.
 intros BA BB HP HEA HEB HQ HI HO.
 pose proof(proj2(source_bounded_accept_binary M SFImpl a b point(succM M k)
  (or_intror(or_intror eq_refl))HP)(conj BA BB))as BP.
 pose proof(proj2(source_bounded_accept_unary M SFEx a exa k(or_intror eq_refl)HEA)BA)as BEA.
 pose proof(proj2(source_bounded_accept_unary M SFEx b exb k(or_intror eq_refl)HEB)BB)as BEB.
 pose proof(proj2(source_bounded_accept_unary M SFAll point qpoint k(or_introl eq_refl)HQ)BP)as BQ.
 pose proof(proj2(source_bounded_accept_binary M SFImpl exa exb inside k
  (or_intror(or_intror eq_refl))HI)(conj BEA BEB))as BI.
 pose proof(proj2(source_bounded_accept_binary M SFImpl qpoint inside out k
  (or_intror(or_intror eq_refl))HO)(conj BQ BI))as BO.
 destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)qpoint)as(b1&c1&n1&H1).
 pose proof(proj2(context_bounded_cons M _ _ _ qpoint b1 c1 n1 k H1)
  (conj BQ(context_bounded_empty M _ _ k)))as C1.
 destruct(environment_cons_total M b1 c1 n1 exa)as(b2&c2&n2&H2).
 pose proof(proj2(context_bounded_cons M b1 c1 n1 exa b2 c2 n2 k H2)(conj BEA C1))as C2.
 destruct(context_shift_total M b2 c2 n2)as(sb&sc&HS).
 assert(MQ:context_member M b2 c2 n2 qpoint).
 { apply(source_cons_tail_inclusion M b1 c1 n1 exa b2 c2 n2 H2).
   apply(proj2(context_member_cons M _ _ _ qpoint b1 c1 n1 qpoint H1)). now left. }
 pose proof(source_full_shifted_universal_hyp M b2 c2 n2 sb sc point qpoint(succM M k)
  (ex_intro _ k C2)HS MQ BP HQ)as PP.
 pose proof(source_full_cons_head M b1 c1 n1 exa b2 c2 n2 k H2 BEA C2)as PEA.
 pose proof(source_full_existential_map_shift M b2 c2 n2 a b exa exb point sb sc HEA HEB HP HS PEA PP)as PEB.
 pose proof(full_source_II M b1 c1 n1 exa exb inside b2 c2 n2(ex_intro _ k(conj BI C1))PEB H2 HI)as PI.
 exact(full_source_II M(zeroM M)(zeroM M)(zeroM M)qpoint inside out b1 c1 n1
  (ex_intro _ k(conj BO(context_bounded_empty M _ _ k)))PI H1 HO).
Qed.

Print Assumptions source_existential_distribution.
