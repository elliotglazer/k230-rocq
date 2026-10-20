(** The exact K-closure witness at arbitrary named input/output roles. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceHierarchySyntax SourcePieceConjunction SourcePieceConjunctionBounds.
Unset Implicit Arguments.
Definition source_reflection_KF_witness M domain level sb sc n K x w out:=
 exists member next lev pc point all inner,
 sf_relation M SFMember w K member /\sf_relation M SFMember x w next /\
 source_LL_instance M(succM M x)(zeroM M)lev /\
 source_piece_conjunction M domain level sb sc n(succM M w)(zeroM M)pc /\
 sf_relation M SFImpl lev pc point /\sf_relation M SFAll point(zeroM M)all /\
 sf_relation M SFAnd next all inner /\sf_relation M SFAnd member inner out.
Theorem source_reflection_KF_witness_total M domain level sb sc n K x w:
 exists out,source_reflection_KF_witness M domain level sb sc n K x w out.
Proof.
 destruct(sf_relation_total M SFMember w K)as(member&HM).
 destruct(sf_relation_total M SFMember x w)as(next&HN).
 destruct(source_LL_instance_total M(succM M x)(zeroM M))as(lev&HL).
 destruct(source_piece_conjunction_total M domain level sb sc n(succM M w)(zeroM M))as(pc&HPC).
 destruct(sf_relation_total M SFImpl lev pc)as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(all&HA).
 destruct(sf_relation_total M SFAnd next all)as(inner&HI).
 destruct(sf_relation_total M SFAnd member inner)as(out&HO).
 exists out,member,next,lev,pc,point,all,inner. auto 15.
Qed.
Theorem source_reflection_KF_witness_functional M domain level sb sc n K x w a b:
 source_reflection_KF_witness M domain level sb sc n K x w a ->source_reflection_KF_witness M domain level sb sc n K x w b ->a=b.
Proof.
 intros(m&t&l&p&q&all&i&HM&HT&HL&HP&HQ&HA&HI&HF)
 (m'&t'&l'&p'&q'&all'&i'&HM'&HT'&HL'&HP'&HQ'&HA'&HI'&HG).
 assert(E:m'=m)by(eapply sf_relation_functional;eassumption). subst m'.
 assert(E:t'=t)by(eapply sf_relation_functional;eassumption). subst t'.
 assert(E:l'=l)by(eapply source_LL_instance_functional;eassumption). subst l'.
 assert(E:p'=p)by(eapply source_piece_conjunction_functional;eassumption). subst p'.
 assert(E:q'=q)by(eapply sf_relation_functional;eassumption). subst q'.
 assert(E:all'=all)by(eapply sf_relation_functional;eassumption). subst all'.
 assert(E:i'=i)by(eapply sf_relation_functional;eassumption). subst i'.
 exact(sf_relation_functional M SFAnd m i a b HF HG).
Qed.
Theorem source_reflection_KF_witness_bounded M domain level sb sc n K x w out k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
 coding_lt M K k ->coding_lt M x k ->coding_lt M w k ->source_reflection_KF_witness M domain level sb sc n K x w out ->source_bounded M out k.
Proof.
 intros HD HL HV BK BX BW(m&t&l&p&q&all&i&HM&HT&HLg&HP&HQ&HA&HI&HF).
 pose proof(source_LL_instance_bounded M(succM M x)(zeroM M)l(succM M k)(proj2(coding_lt_succ_cancel M x k)BX)(coding_zero_lt_succ M k)HLg)as BL.
 pose proof(source_piece_conjunction_bounded M n domain level sb sc(succM M w)(zeroM M)p(succM M k)HD HL HV(proj2(coding_lt_succ_cancel M w k)BW)(coding_zero_lt_succ M k)HP)as BP.
 pose proof(proj2(source_bounded_accept_binary M SFImpl l p q _ (or_intror(or_intror eq_refl))HQ)(conj BL BP))as BQ.
 pose proof(proj2(source_bounded_accept_unary M SFAll q all k(or_introl eq_refl)HA)BQ)as BA.
 pose proof(proj2(source_bounded_accept_atom M SFMember w K m k(or_introl eq_refl)HM)(conj BW BK))as BM.
 pose proof(proj2(source_bounded_accept_atom M SFMember x w t k(or_introl eq_refl)HT)(conj BX BW))as BT.
 pose proof(proj2(source_bounded_accept_binary M SFAnd t all i k(or_introl eq_refl)HI)(conj BT BA))as BI.
 exact(proj2(source_bounded_accept_binary M SFAnd m i out k(or_introl eq_refl)HF)(conj BM BI)).
Qed.
Print Assumptions source_reflection_KF_witness_total.
Print Assumptions source_reflection_KF_witness_functional.
Print Assumptions source_reflection_KF_witness_bounded.
