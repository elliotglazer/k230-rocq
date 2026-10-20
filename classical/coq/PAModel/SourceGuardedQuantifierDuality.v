(** Actual guarded quantifier duality: All(G implies A) iff not Ex(G and
    not A), for arbitrary internal matrices and ordinary proof contexts. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourceQuantifierClassicalDuality
  SourceEmptyExistentialMap SourceGuardedNegationProgram.
Unset Implicit Arguments.

Theorem source_full_guarded_all_from_not_exists_neg M b c n guard a implication negA both exBoth notBoth all k:
  context_bounded M b c n k ->source_bounded M guard(succM M k) ->source_bounded M a(succM M k) ->
  sf_relation M SFImpl guard a implication ->sf_relation M SFImpl a(zeroM M)negA ->
  sf_relation M SFAnd guard negA both ->sf_relation M SFEx both(zeroM M)exBoth ->
  sf_relation M SFImpl exBoth(zeroM M)notBoth ->sf_relation M SFAll implication(zeroM M)all ->
  source_full_prv M b c n notBoth ->source_full_prv M b c n all.
Proof.
  intros BC BG BA HI HNA HB HE HN HAll PN.
  pose proof(proj2(source_bounded_accept_binary M SFImpl guard a implication(succM M k)
    (or_intror(or_intror eq_refl))HI)(conj BG BA))as BI.
  pose proof(proj2(source_bounded_accept_binary M SFImpl a(zeroM M)negA(succM M k)
    (or_intror(or_intror eq_refl))HNA)(conj BA(source_bounded_accept_falsity M(succM M k))))as BNA.
  pose proof(proj2(source_bounded_accept_binary M SFAnd guard negA both(succM M k)(or_introl eq_refl)HB)(conj BG BNA))as BB.
  destruct(sf_relation_total M SFImpl implication(zeroM M))as(negImp&HNI).
  pose proof(proj2(source_bounded_accept_binary M SFImpl implication(zeroM M)negImp(succM M k)
    (or_intror(or_intror eq_refl))HNI)(conj BI(source_bounded_accept_falsity M(succM M k))))as BNI.
  destruct(sf_relation_total M SFEx negImp(zeroM M))as(exNeg&HEx).
  destruct(sf_relation_total M SFImpl exNeg(zeroM M))as(notNeg&HNot).
  destruct(sf_relation_total M SFImpl negImp both)as(point&HPoint).
  pose proof(source_guarded_negation_empty M false guard a implication negImp negA both point(succM M k)
    BG BA HI HNI HNA HB HPoint)as PPoint.
  pose proof(source_full_not_exists_contravariant_from_empty M b c n negImp both exNeg exBoth point notNeg notBoth k
    BC BNI BB HEx HE HPoint HNot HN PPoint PN)as PNotNeg.
  exact(source_full_all_from_not_ex_neg M b c n implication negImp exNeg notNeg all k BC BI HNI HEx HNot HAll PNotNeg).
Qed.

Theorem source_full_not_exists_neg_from_guarded_all M b c n guard a implication negA both exBoth notBoth all k:
  context_bounded M b c n k ->source_bounded M guard(succM M k) ->source_bounded M a(succM M k) ->
  sf_relation M SFImpl guard a implication ->sf_relation M SFImpl a(zeroM M)negA ->
  sf_relation M SFAnd guard negA both ->sf_relation M SFEx both(zeroM M)exBoth ->
  sf_relation M SFImpl exBoth(zeroM M)notBoth ->sf_relation M SFAll implication(zeroM M)all ->
  source_full_prv M b c n all ->source_full_prv M b c n notBoth.
Proof.
  intros BC BG BA HI HNA HB HE HN HAll PA.
  pose proof(proj2(source_bounded_accept_binary M SFImpl guard a implication(succM M k)
    (or_intror(or_intror eq_refl))HI)(conj BG BA))as BI.
  pose proof(proj2(source_bounded_accept_binary M SFImpl a(zeroM M)negA(succM M k)
    (or_intror(or_intror eq_refl))HNA)(conj BA(source_bounded_accept_falsity M(succM M k))))as BNA.
  pose proof(proj2(source_bounded_accept_binary M SFAnd guard negA both(succM M k)(or_introl eq_refl)HB)(conj BG BNA))as BB.
  destruct(sf_relation_total M SFImpl implication(zeroM M))as(negImp&HNI).
  pose proof(proj2(source_bounded_accept_binary M SFImpl implication(zeroM M)negImp(succM M k)
    (or_intror(or_intror eq_refl))HNI)(conj BI(source_bounded_accept_falsity M(succM M k))))as BNI.
  destruct(sf_relation_total M SFEx negImp(zeroM M))as(exNeg&HEx).
  destruct(sf_relation_total M SFImpl exNeg(zeroM M))as(notNeg&HNot).
  pose proof(source_full_not_ex_neg_from_all M b c n implication negImp exNeg notNeg all k BC BI HNI HEx HNot HAll PA)as PNotNeg.
  destruct(sf_relation_total M SFImpl both negImp)as(point&HPoint).
  pose proof(source_guarded_negation_empty M true guard a implication negImp negA both point(succM M k)
    BG BA HI HNI HNA HB HPoint)as PPoint.
  exact(source_full_not_exists_contravariant_from_empty M b c n both negImp exBoth exNeg point notBoth notNeg k
    BC BB BNI HE HEx HPoint HN HNot PPoint PNotNeg).
Qed.
Print Assumptions source_full_guarded_all_from_not_exists_neg.
Print Assumptions source_full_not_exists_neg_from_guarded_all.
