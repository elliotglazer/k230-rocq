(** Exact K-closure profile of the pinned reflection proof.
 Under the three binders [X,w,k], level is LL(2,0) and PCf has roles(1,0). *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceHierarchySyntax SourcePieceConjunction SourcePieceConjunctionBounds.
Unset Implicit Arguments.
Definition source_reflection_KF M domain level sb sc n K out:=
 exists guard lev pc point all memberK next inner body ex tail,
 sf_relation M SFMember(zeroM M)(succM M K)guard /\
 source_LL_instance M(code_numeral M 2)(zeroM M)lev /\
 source_piece_conjunction M domain level sb sc n(code_numeral M 1)(zeroM M)pc /\
 sf_relation M SFImpl lev pc point /\sf_relation M SFAll point(zeroM M)all /\
 sf_relation M SFMember(zeroM M)(succM M(succM M K))memberK /\
 sf_relation M SFMember(code_numeral M 1)(zeroM M)next /\
 sf_relation M SFAnd next all inner /\sf_relation M SFAnd memberK inner body /\
 sf_relation M SFEx body(zeroM M)ex /\sf_relation M SFImpl guard ex tail /\sf_relation M SFAll tail(zeroM M)out.
Theorem source_reflection_KF_total M domain level sb sc n K:exists out,source_reflection_KF M domain level sb sc n K out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M K))as(guard&HGuard).
 destruct(source_LL_instance_total M(code_numeral M 2)(zeroM M))as(lev&HL).
 destruct(source_piece_conjunction_total M domain level sb sc n(code_numeral M 1)(zeroM M))as(pc&HPC).
 destruct(sf_relation_total M SFImpl lev pc)as(point&HPoint).
 destruct(sf_relation_total M SFAll point(zeroM M))as(all&HAll).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M(succM M K)))as(memberK&HMK).
 destruct(sf_relation_total M SFMember(code_numeral M 1)(zeroM M))as(next&HN).
 destruct(sf_relation_total M SFAnd next all)as(inner&HInner).
 destruct(sf_relation_total M SFAnd memberK inner)as(body&HBody).
 destruct(sf_relation_total M SFEx body(zeroM M))as(ex&HEx).
 destruct(sf_relation_total M SFImpl guard ex)as(tail&HTail).
 destruct(sf_relation_total M SFAll tail(zeroM M))as(out&HOut).
 exists out,guard,lev,pc,point,all,memberK,next,inner,body,ex,tail. auto 20.
Qed.
Theorem source_reflection_KF_functional M domain level sb sc n K x y:
 source_reflection_KF M domain level sb sc n K x ->source_reflection_KF M domain level sb sc n K y ->x=y.
Proof.
 intros(g&l&p&q&a&m&t&i&b&e&u&HG&HL&HP&HQ&HA&HM&HT&HI&HB&HE&HU&HX)
 (g'&l'&p'&q'&a'&m'&t'&i'&b'&e'&u'&HG'&HL'&HP'&HQ'&HA'&HM'&HT'&HI'&HB'&HE'&HU'&HY).
 assert(E:g'=g)by(eapply sf_relation_functional;eassumption). subst g'.
 assert(E:l'=l)by(eapply source_LL_instance_functional;eassumption). subst l'.
 assert(E:p'=p)by(eapply source_piece_conjunction_functional;eassumption). subst p'.
 assert(E:q'=q)by(eapply sf_relation_functional;eassumption). subst q'.
 assert(E:a'=a)by(eapply sf_relation_functional;eassumption). subst a'.
 assert(E:m'=m)by(eapply sf_relation_functional;eassumption). subst m'.
 assert(E:t'=t)by(eapply sf_relation_functional;eassumption). subst t'.
 assert(E:i'=i)by(eapply sf_relation_functional;eassumption). subst i'.
 assert(E:b'=b)by(eapply sf_relation_functional;eassumption). subst b'.
 assert(E:e'=e)by(eapply sf_relation_functional;eassumption). subst e'.
 assert(E:u'=u)by(eapply sf_relation_functional;eassumption). subst u'.
 exact(sf_relation_functional M SFAll u(zeroM M)x y HX HY).
Qed.
Theorem source_reflection_KF_bounded M domain level sb sc n K out k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
 coding_lt M K k ->source_reflection_KF M domain level sb sc n K out ->source_bounded M out k.
Proof.
 intros HD HL HV BK(g&l&p&q&a&m&t&i&b&e&u&HG&HLg&HP&HQ&HA&HM&HT&HI&HB&HE&HU&HX).
 assert(B0:coding_lt M(zeroM M)(succM M(succM M(succM M k))))by(apply coding_zero_lt_succ).
 assert(B1:coding_lt M(code_numeral M 1)(succM M(succM M(succM M k))))by(apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M(succM M k))));apply coding_zero_lt_succ).
 assert(B2:coding_lt M(code_numeral M 2)(succM M(succM M(succM M k))))by(apply(proj2(coding_lt_succ_cancel M(code_numeral M 1)(succM M(succM M k))));apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k)));apply coding_zero_lt_succ).
 pose proof(source_LL_instance_bounded M(code_numeral M 2)(zeroM M)l(succM M(succM M(succM M k)))B2 B0 HLg)as BL.
 pose proof(source_piece_conjunction_bounded M n domain level sb sc(code_numeral M 1)(zeroM M)p(succM M(succM M(succM M k)))HD HL HV B1 B0 HP)as BP.
 pose proof(proj2(source_bounded_accept_binary M SFImpl l p q _ (or_intror(or_intror eq_refl))HQ)(conj BL BP))as BQ.
 pose proof(proj2(source_bounded_accept_unary M SFAll q a _ (or_introl eq_refl)HA)BQ)as BA.
 assert(BM:source_bounded M m(succM M(succM M k))).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ m _ (or_introl eq_refl)HM)). split;[apply coding_zero_lt_succ|]. apply(proj2(coding_lt_succ_cancel M(succM M K)(succM M k))), (proj2(coding_lt_succ_cancel M K k));exact BK. }
 assert(BT:source_bounded M t(succM M(succM M k))).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ t _ (or_introl eq_refl)HT)). split;[apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k)))|];apply coding_zero_lt_succ. }
 pose proof(proj2(source_bounded_accept_binary M SFAnd t a i _ (or_introl eq_refl)HI)(conj BT BA))as BI.
 pose proof(proj2(source_bounded_accept_binary M SFAnd m i b _ (or_introl eq_refl)HB)(conj BM BI))as BB.
 pose proof(proj2(source_bounded_accept_unary M SFEx b e _ (or_intror eq_refl)HE)BB)as BE.
 assert(BG:source_bounded M g(succM M k)).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ g _ (or_introl eq_refl)HG)). split;[apply coding_zero_lt_succ|]. exact(proj2(coding_lt_succ_cancel M K k)BK). }
 pose proof(proj2(source_bounded_accept_binary M SFImpl g e u _ (or_intror(or_intror eq_refl))HU)(conj BG BE))as BU.
 exact(proj2(source_bounded_accept_unary M SFAll u out k(or_introl eq_refl)HX)BU).
Qed.
Print Assumptions source_reflection_KF_total.
Print Assumptions source_reflection_KF_functional.
Print Assumptions source_reflection_KF_bounded.
