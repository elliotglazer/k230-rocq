(** Literal Clos(phi,a,Y) with genuine application of an arbitrary
    internally coded binary matrix at the input/output roles 1,0. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceRecursionBinaryInstance SourceFiniteCutoffShift.
Unset Implicit Arguments.
Definition source_rec_closure M phi a Y out:=exists initial guard binary member body ex point all,
  sf_relation M SFMember a Y initial /\
  sf_relation M SFMember(zeroM M)(succM M Y)guard /\
  source_rec_binary M phi(code_numeral M 1)(zeroM M)binary /\
  sf_relation M SFMember(zeroM M)(succM M(succM M Y))member /\
  sf_relation M SFAnd binary member body /\sf_relation M SFEx body(zeroM M)ex /\
  sf_relation M SFImpl guard ex point /\sf_relation M SFAll point(zeroM M)all /\
  sf_relation M SFAnd initial all out.

Theorem source_rec_closure_total M phi a Y:exists out,source_rec_closure M phi a Y out.
Proof.
  destruct(sf_relation_total M SFMember a Y)as(initial&HI).
  destruct(sf_relation_total M SFMember(zeroM M)(succM M Y))as(guard&HG).
  destruct(source_rec_binary_total M phi(code_numeral M 1)(zeroM M))as(binary&HB).
  destruct(sf_relation_total M SFMember(zeroM M)(succM M(succM M Y)))as(member&HM).
  destruct(sf_relation_total M SFAnd binary member)as(body&HBody).
  destruct(sf_relation_total M SFEx body(zeroM M))as(ex&HE).
  destruct(sf_relation_total M SFImpl guard ex)as(point&HP).
  destruct(sf_relation_total M SFAll point(zeroM M))as(all&HA).
  destruct(sf_relation_total M SFAnd initial all)as(out&HO).
  exists out,initial,guard,binary,member,body,ex,point,all. repeat first[assumption|split].
Qed.

Theorem source_rec_closure_functional M phi a Y x y:
  source_rec_closure M phi a Y x ->source_rec_closure M phi a Y y ->x=y.
Proof.
  intros(i&g&b&m&d&e&p&f&HI&HG&HB&HM&HD&HE&HP&HF&HX)
    (i'&g'&b'&m'&d'&e'&p'&f'&HI'&HG'&HB'&HM'&HD'&HE'&HP'&HF'&HY).
  pose proof(sf_relation_functional M SFMember a Y i' i HI' HI)as E. subst i'.
  pose proof(sf_relation_functional M SFMember(zeroM M)(succM M Y)g' g HG' HG)as E. subst g'.
  pose proof(source_rec_binary_functional M phi(code_numeral M 1)(zeroM M)b' b HB' HB)as E. subst b'.
  pose proof(sf_relation_functional M SFMember(zeroM M)(succM M(succM M Y))m' m HM' HM)as E. subst m'.
  pose proof(sf_relation_functional M SFAnd b m d' d HD' HD)as E. subst d'.
  pose proof(sf_relation_functional M SFEx d(zeroM M)e' e HE' HE)as E. subst e'.
  pose proof(sf_relation_functional M SFImpl g e p' p HP' HP)as E. subst p'.
  pose proof(sf_relation_functional M SFAll p(zeroM M)f' f HF' HF)as E. subst f'.
  exact(sf_relation_functional M SFAnd i f x y HX HY).
Qed.

Theorem source_rec_closure_bounded M phi a Y out k:
  source_bounded M phi(code_numeral M 2) ->coding_lt M a k ->coding_lt M Y k ->
  source_rec_closure M phi a Y out ->source_bounded M out k.
Proof.
  intros BP BA BY(i&g&b&m&d&e&p&f&HI&HG&HB&HM&HD&HE&HP&HF&HO).
  pose proof(proj2(source_bounded_accept_atom M SFMember a Y i k(or_introl eq_refl)HI)(conj BA BY))as BI.
  pose proof(proj2(coding_lt_succ_cancel M Y k)BY)as SY.
  pose proof(proj2(coding_lt_succ_cancel M(succM M Y)(succM M k))SY)as SSY.
  assert(BG:source_bounded M g(succM M k)).
  { apply(proj2(source_bounded_accept_atom M SFMember _ _ g(succM M k)(or_introl eq_refl)HG)).
    split;[apply coding_zero_lt_succ|exact SY]. }
  assert(BB:source_bounded M b(succM M(succM M k))).
  { apply(source_rec_binary_bounded M phi(code_numeral M 1)(zeroM M)b(succM M(succM M k))BP);
      [apply coding_lt_succ_cancel,coding_zero_lt_succ|apply coding_zero_lt_succ|exact HB]. }
  assert(BM:source_bounded M m(succM M(succM M k))).
  { apply(proj2(source_bounded_accept_atom M SFMember _ _ m(succM M(succM M k))(or_introl eq_refl)HM)).
    split;[apply coding_zero_lt_succ|exact SSY]. }
  pose proof(proj2(source_bounded_accept_binary M SFAnd b m d(succM M(succM M k))(or_introl eq_refl)HD)(conj BB BM))as BD.
  pose proof(proj2(source_bounded_accept_unary M SFEx d e(succM M k)(or_intror eq_refl)HE)BD)as BE.
  pose proof(proj2(source_bounded_accept_binary M SFImpl g e p(succM M k)(or_intror(or_intror eq_refl))HP)(conj BG BE))as BPoint.
  pose proof(proj2(source_bounded_accept_unary M SFAll p f k(or_introl eq_refl)HF)BPoint)as BF.
  exact(proj2(source_bounded_accept_binary M SFAnd i f out k(or_introl eq_refl)HO)(conj BI BF)).
Qed.
Print Assumptions source_rec_closure_total.
Print Assumptions source_rec_closure_functional.
Print Assumptions source_rec_closure_bounded.
