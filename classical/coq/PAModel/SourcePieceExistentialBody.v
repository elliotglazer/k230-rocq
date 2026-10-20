(** Named ordinal/Pc witness bodies and their actual source renamings. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalInstantiation SourceDomainInstances SourceDomainInstanceRenaming
  SourceOrdinalPredicate SourcePieceClosure SourcePieceRenaming.
Unset Implicit Arguments.

Definition source_piece_existential_body M domain level count phi d X body:=exists ordinal pc,
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal /\source_pc_instance M domain level count phi d X pc /\
  sf_relation M SFAnd ordinal pc body.

Theorem source_piece_existential_body_total M domain level count phi d X:
  exists body,source_piece_existential_body M domain level count phi d X body.
Proof.
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)d) as(ordinal&HO).
  destruct(source_pc_instance_total M domain level count phi d X) as(pc&HPC).
  destruct(sf_relation_total M SFAnd ordinal pc) as(body&HB). exists body,ordinal,pc. auto.
Qed.

Theorem source_piece_existential_body_renaming M domain level count phi d X body rb rc rn delta e Y out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_bounded M phi(succM M count) ->
  source_piece_existential_body M domain level count phi d X body ->numerical_renaming M body rb rc rn delta out ->
  renaming_lookup M rb rc rn delta d e ->renaming_lookup M rb rc rn delta X Y ->
  source_piece_existential_body M domain level count phi e Y out.
Proof.
  intros HD HL HB(ordinal&pc&HO&HPC&HBody)HR HDE HXY.
  destruct(proj1(numerical_renaming_binary M SFAnd ordinal pc body rb rc rn delta out(or_introl eq_refl)HBody)HR)
    as(ordinal'&pc'&HRO&HRPC&HBody').
  exists ordinal',pc'. split.
  - exact(source_domain_instance_renaming M(source_ordinal_predicate_code M)d ordinal rb rc rn delta ordinal' e
      (source_ordinal_predicate_bounded M)HO HRO HDE).
  - split;[|exact HBody'].
    exact(source_pc_instance_renaming M domain level count phi d X pc rb rc rn delta e Y pc' HD HL HB HPC HRPC HDE HXY).
Qed.

Theorem source_piece_existential_body_bounded M domain level count phi d X body k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_bounded M phi(succM M count) ->
  coding_lt M d k ->coding_lt M X k ->source_piece_existential_body M domain level count phi d X body ->source_bounded M body k.
Proof.
  intros HD HL HB HDk HX(ordinal&pc&HO&HPC&HBody).
  exact(proj2(source_bounded_accept_binary M SFAnd ordinal pc body k(or_introl eq_refl)HBody)
    (conj(source_domain_instance_bound M(source_ordinal_predicate_code M)d ordinal k(source_ordinal_predicate_bounded M)HDk HO)
      (source_pc_instance_bounded M domain level count phi d X pc k HD HL HB HDk HX HPC))).
Qed.

Print Assumptions source_piece_existential_body_total.
Print Assumptions source_piece_existential_body_renaming.
Print Assumptions source_piece_existential_body_bounded.
