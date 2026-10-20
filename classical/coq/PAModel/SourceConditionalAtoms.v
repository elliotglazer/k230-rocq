(** Actual conditional atom transport, from internally coded equality proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceConditionalProofs SourceConditionalComposition SourceEqualityAtomFacts SourceZFRProvability.
Unset Implicit Arguments.
Lemma source_equality_atom_is_atom equality:source_equality_atom equality=SFMember \/source_equality_atom equality=SFEqual.
Proof. destruct equality;cbn[source_equality_atom];auto. Qed.
Theorem source_conditional_equal_symmetric M condition x y equal reverse k:
 source_bounded M condition k ->coding_lt M x k ->coding_lt M y k ->
 sf_relation M SFEqual x y equal ->sf_relation M SFEqual y x reverse ->
 source_conditional_fact M condition equal ->source_conditional_fact M condition reverse.
Proof.
 intros BC BX BY HE HR PF.
 pose proof(proj2(source_bounded_accept_atom M SFEqual x y equal k(or_intror eq_refl)HE)(conj BX BY))as BE.
 pose proof(proj2(source_bounded_accept_atom M SFEqual y x reverse k(or_intror eq_refl)HR)(conj BY BX))as BR.
 destruct(sf_relation_total M SFImpl equal reverse)as(law&HL).
 exact(source_conditional_fact_consequence M condition equal reverse law k BC BE BR HL
  (source_zfr_equal_symmetric M x y equal reverse law HE HR HL)PF).
Qed.

Theorem source_conditional_atom M equality condition a b d e left right equal1 equal2 k:
 source_bounded M condition k ->coding_lt M a k ->coding_lt M b k ->coding_lt M d k ->coding_lt M e k ->
 sf_relation M(source_equality_atom equality)a b left ->sf_relation M(source_equality_atom equality)d e right ->
 sf_relation M SFEqual a d equal1 ->sf_relation M SFEqual b e equal2 ->
 source_conditional_fact M condition equal1 ->source_conditional_fact M condition equal2 ->
 source_conditional_implies M condition left right.
Proof.
 intros BC BA BB BD BE HL HR HE1 HE2 P1 P2.
 set(h:=source_equality_atom equality).
 pose proof(source_equality_atom_is_atom equality)as HH.
 pose proof(proj2(source_bounded_accept_atom M h a b left k HH HL)(conj BA BB))as BL.
 pose proof(proj2(source_bounded_accept_atom M h d e right k HH HR)(conj BD BE))as BR.
 pose proof(proj2(source_bounded_accept_atom M SFEqual a d equal1 k(or_intror eq_refl)HE1)(conj BA BD))as B1.
 pose proof(proj2(source_bounded_accept_atom M SFEqual b e equal2 k(or_intror eq_refl)HE2)(conj BB BE))as B2.
 destruct(sf_relation_total M h d b)as(middle&HM).
 pose proof(proj2(source_bounded_accept_atom M h d b middle k HH HM)(conj BD BB))as BM.
 assert(First:source_conditional_implies M condition left middle).
 { intros point HP.
   pose proof(proj2(source_bounded_accept_binary M SFImpl left middle point k(or_intror(or_intror eq_refl))HP)(conj BL BM))as BP.
   destruct(sf_relation_total M SFImpl equal1 point)as(law&HLaw).
   exact(source_conditional_fact_consequence M condition equal1 point law k BC B1 BP HLaw
    (source_zfr_atom_equal_left M equality a d b equal1 left middle point law HE1 HL HM HP HLaw)P1). }
 assert(Second:source_conditional_implies M condition middle right).
 { intros point HP.
   pose proof(proj2(source_bounded_accept_binary M SFImpl middle right point k(or_intror(or_intror eq_refl))HP)(conj BM BR))as BP.
   destruct(sf_relation_total M SFImpl equal2 point)as(law&HLaw).
   exact(source_conditional_fact_consequence M condition equal2 point law k BC B2 BP HLaw
    (source_zfr_atom_equal_right M equality b e d equal2 middle right point law HE2 HM HR HP HLaw)P2). }
 exact(source_conditional_implies_trans M condition left middle right k BC BL BM BR First Second).
Qed.
Print Assumptions source_conditional_equal_symmetric.
Print Assumptions source_conditional_atom.
