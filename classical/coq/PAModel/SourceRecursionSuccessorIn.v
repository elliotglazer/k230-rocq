(** An actual successor in a named set, and successor closure of that set. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport NumericalSubstitutionMaps NumericalSubstitution.
Unset Implicit Arguments.
Definition source_rec_successor_in M z X out:=exists successor member body,
 source_rec_successor M(succM M z)(zeroM M)successor /\sf_relation M SFMember(zeroM M)(succM M X)member /\
 sf_relation M SFAnd successor member body /\sf_relation M SFEx body(zeroM M)out.
Definition source_rec_successor_closed M X out:=exists member ex point,
 sf_relation M SFMember(zeroM M)(succM M X)member /\source_rec_successor_in M(zeroM M)(succM M X)ex /\
 sf_relation M SFImpl member ex point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_rec_successor_in_total M z X:exists out,source_rec_successor_in M z X out.
Proof.
 destruct(source_rec_successor_total M(succM M z)(zeroM M))as(successor&HS).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M X))as(member&HM).
 destruct(sf_relation_total M SFAnd successor member)as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,successor,member,body. auto.
Qed.
Theorem source_rec_successor_closed_total M X:exists out,source_rec_successor_closed M X out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M X))as(member&HM).
 destruct(source_rec_successor_in_total M(zeroM M)(succM M X))as(ex&HE).
 destruct(sf_relation_total M SFImpl member ex)as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(out&HO). exists out,member,ex,point. auto.
Qed.
Theorem source_rec_successor_in_bounded M z X out k:
 coding_lt M z k ->coding_lt M X k ->source_rec_successor_in M z X out ->source_bounded M out k.
Proof.
 intros BZ BX(successor&member&body&HS&HM&HB&HO).
 pose proof(source_rec_successor_bounded M(succM M z)(zeroM M)successor(succM M k)
  (proj2(coding_lt_succ_cancel M z k)BZ)(coding_zero_lt_succ M k)HS)as BS.
 pose proof(proj2(source_bounded_accept_atom M SFMember _ _ member(succM M k)(or_introl eq_refl)HM)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M X k)BX)))as BM.
 pose proof(proj2(source_bounded_accept_binary M SFAnd successor member body(succM M k)(or_introl eq_refl)HB)(conj BS BM))as BB.
 exact(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)BB).
Qed.
Theorem source_rec_successor_closed_bounded M X out k:
 coding_lt M X k ->source_rec_successor_closed M X out ->source_bounded M out k.
Proof.
 intros BX(member&ex&point&HM&HE&HP&HO).
 pose proof(proj2(source_bounded_accept_atom M SFMember _ _ member(succM M k)(or_introl eq_refl)HM)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M X k)BX)))as BM.
 pose proof(source_rec_successor_in_bounded M(zeroM M)(succM M X)ex(succM M k)(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M X k)BX)HE)as BE.
 pose proof(proj2(source_bounded_accept_binary M SFImpl member ex point(succM M k)(or_intror(or_intror eq_refl))HP)(conj BM BE))as BP.
 exact(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HO)BP).
Qed.
Theorem source_rec_successor_in_substitution M z X out z' X' out' rb rc rn base:
 source_rec_successor_in M z X out ->source_rec_successor_in M z' X' out' ->
 substitution_lookup M rb rc rn base z z' ->substitution_lookup M rb rc rn base X X' ->numerical_substitution M out rb rc rn base out'.
Proof.
 intros(succ&member&body&HS&HM&HB&HO)(succ'&member'&body'&HS'&HM'&HB'&HO')HZ HX.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 pose proof(source_rec_successor_substitution M(succM M z)(zeroM M)succ(succM M z')(zeroM M)succ' lb lc ln(succM M base)HS HS'
  (proj2(proj2 HL)z z' HZ)(proj1(proj2 HL)))as HSucc.
 assert(HMember:numerical_substitution M member lb lc ln(succM M base)member').
 { apply(proj2(numerical_substitution_member M _ _ member lb lc ln(succM M base)member' HM)).
   exists(zeroM M),(succM M X'). exact(conj(proj1(proj2 HL))(conj(proj2(proj2 HL)X X' HX)HM')). }
 assert(HBody:numerical_substitution M body lb lc ln(succM M base)body').
 { apply(proj2(numerical_substitution_binary M SFAnd succ member body lb lc ln(succM M base)body'(or_introl eq_refl)HB)).
   exists succ',member'. auto. }
 apply(proj2(numerical_substitution_quantifier M false body out rb rc rn base out' HO)).
 exists lb,lc,ln,body'. auto.
Qed.
Print Assumptions source_rec_successor_in_total.
Print Assumptions source_rec_successor_closed_total.
Print Assumptions source_rec_successor_in_bounded.
Print Assumptions source_rec_successor_closed_bounded.
Print Assumptions source_rec_successor_in_substitution.
