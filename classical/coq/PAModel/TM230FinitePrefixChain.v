(** Actual beta histories for a finite physical prefix followed by an internally
    finite register suffix. Both source value lookups and suffix words are kept. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 BetaPacking CodeExpressions TM230UnaryBlocks TM230RegisterWords TM230CarryChainSyntax.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Section Prefix.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S O).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Add Ring finite_prefix_ring:(model_semiring M).

Lemma prefix_add_succ_right x y:x+S y=S(x+y).
Proof. rewrite(Arithmetic.add_comm M x(S y)),Arithmetic.add_succ,Arithmetic.add_comm;reflexivity. Qed.
Lemma prefix_numeral_lt i n:(i<n)%nat->coding_lt M(N i)(N n).
Proof.
 induction n as[|n IH]in i|-*;intro Hi;[lia|].
 destruct i as[|i];[apply coding_zero_lt_succ|].
 apply(proj2(coding_lt_succ_cancel M(N i)(N n)));apply IH;lia.
Qed.
Lemma prefix_lt_add_right x y z:coding_lt M x y->coding_lt M x(y+z).
Proof. intros[d E];exists(d+z);rewrite E,Arithmetic.add_succ;f_equal;ring. Qed.
Lemma prefix_beta_iff b c d e i j:
 (forall x,beta M b c i x->beta M d e j x)->
 forall x,beta M b c i x<->beta M d e j x.
Proof.
 intros H x;split;[apply H|intro Hx].
 destruct(beta_total M b c i)as[y Hy].
 assert(E:x=y)by(eapply beta_unique;[exact Hx|exact(H y Hy)]).
 now rewrite E.
Qed.

Theorem machine230_chain_prepend vb vc wb wc count first last value head:
 machine230_carry_chain M vb vc wb wc count ->
 beta M wb wc O first ->beta M wb wc count last ->
 machine230_unary_block M value first head ->
 exists dv ev dw ew,
 machine230_carry_chain M dv ev dw ew(S count) /\
 beta M dw ew O head /\beta M dw ew(S count)last /\beta M dv ev O value /\
 (forall i x,coding_lt M i count->(beta M vb vc i x<->beta M dv ev(S i)x)) /\
 (forall i x,coding_lt M i(S count)->(beta M wb wc i x<->beta M dw ew(S i)x)).
Proof.
 intros HC HF HT HB.
 destruct(beta_concatenate M value value one vb vc count)as[dv[ev[HV0 HVS]]].
 destruct(beta_concatenate M head head one wb wc(S count))as[dw[ew[HW0 HWS]]].
 assert(V0:beta M dv ev O value)by(apply HV0;[apply coding_zero_lt_succ|apply beta_singleton]).
 assert(W0:beta M dw ew O head)by(apply HW0;[apply coding_zero_lt_succ|apply beta_singleton]).
 assert(VS:forall i x,coding_lt M i count->(beta M vb vc i x<->beta M dv ev(S i)x)).
 { intros i x Hi. apply prefix_beta_iff. intros y Hy.
   pose proof(HVS i y Hi Hy)as H. rewrite Arithmetic.add_succ,Arithmetic.add_zero in H;exact H. }
 assert(WS:forall i x,coding_lt M i(S count)->(beta M wb wc i x<->beta M dw ew(S i)x)).
 { intros i x Hi. apply prefix_beta_iff. intros y Hy.
   pose proof(HWS i y Hi Hy)as H. rewrite Arithmetic.add_succ,Arithmetic.add_zero in H;exact H. }
 exists dv,ev,dw,ew. split.
 - intros i Hi. destruct(@Peano.zero_or_succ D(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H)i)as[Ei|[j Ei]];subst i.
   + exists value,head,first. split;[exact V0|]. split;[exact W0|].
     split;[apply(proj1(WS O first(coding_zero_lt_succ M count)));exact HF|exact HB].
   + assert(Hj:coding_lt M j count)by(now apply coding_lt_succ_cancel).
     destruct(HC j Hj)as[v[w[next[Hv[Hw[Hnext Hblock]]]]]].
     exists v,w,next. split;[apply(proj1(VS j v Hj));exact Hv|]. split.
     *apply(proj1(WS j w(proj2(coding_lt_succ_cases M j count)(or_introl Hj))));exact Hw.
     *split;[apply(proj1(WS(S j)next(proj2(coding_lt_succ_cancel M j count)Hj)));exact Hnext|exact Hblock].
 - split;[exact W0|]. split.
   + apply(proj1(WS count last(coding_lt_succ M count)));exact HT.
   + split;[exact V0|]. split;assumption.
Qed.

Theorem machine230_finite_prefix_chain values vb vc wb wc count first last prefix:
 machine230_carry_chain M vb vc wb wc count ->
 beta M wb wc O first ->beta M wb wc count last ->
 machine230_blocks_at M(length values)(fun idx=>nth idx values O)first prefix ->
 exists dv ev dw ew,
 machine230_carry_chain M dv ev dw ew(N(length values)+count) /\
 beta M dw ew O prefix /\beta M dw ew(N(length values)+count)last /\
 (forall j,(j<length values)%nat->beta M dv ev(N j)(nth j values O)) /\
 (forall i x,coding_lt M i count->
    (beta M vb vc i x<->beta M dv ev(N(length values)+i)x)) /\
 (forall i x,coding_lt M i(S count)->
    (beta M wb wc i x<->beta M dw ew(N(length values)+i)x)).
Proof.
 intros HC HF HT. induction values as[|value values IH]in prefix|-*;intro HB.
 - change(prefix=first)in HB;subst prefix. exists vb,vc,wb,wc.
   cbn[length code_numeral];rewrite Arithmetic.add_zero.
   split;[exact HC|]. split;[exact HF|]. split;[exact HT|]. split.
   +intros j Hj;lia.
   +split;intros i x Hi;rewrite Arithmetic.add_zero;reflexivity.
 - change(exists middle,
     machine230_blocks_at M(length values)(fun idx=>nth idx values O)first middle /\
     machine230_unary_block M value middle prefix)in HB.
   destruct HB as[middle[Hrest Hhead]].
   destruct(IH middle Hrest)as[av[ac[aw[ad[HA[HA0[HAN[HAV[HASV HASW]]]]]]]]].
   destruct(machine230_chain_prepend av ac aw ad(N(length values)+count)middle last value prefix
     HA HA0 HAN Hhead)as[dv[ev[dw[ew[HD[HD0[HDN[HDV[HDSV HDSW]]]]]]]]].
   exists dv,ev,dw,ew. cbn[length].
   change(machine230_carry_chain M dv ev dw ew(S(N(length values))+count) /\
    beta M dw ew O prefix /\beta M dw ew(S(N(length values))+count)last /\
    (forall j,(j<Datatypes.S(length values))%nat->beta M dv ev(N j)(nth j(value::values)O)) /\
    (forall i x,coding_lt M i count->(beta M vb vc i x<->beta M dv ev(S(N(length values))+i)x)) /\
    (forall i x,coding_lt M i(S count)->(beta M wb wc i x<->beta M dw ew(S(N(length values))+i)x))).
   rewrite(Arithmetic.add_succ M(N(length values))count).
   split;[exact HD|]. split;[exact HD0|]. split;[exact HDN|]. split.
   + intros j Hj;destruct j as[|j];[exact HDV|].
     change(beta M dv ev(S(N j))(nth j values O)).
     apply(proj1(HDSV(N j)(nth j values O)
       (prefix_lt_add_right(N j)(N(length values))count(prefix_numeral_lt j(length values)ltac:(lia))))).
     apply HAV;lia.
   + split;intros i x Hi;rewrite Arithmetic.add_succ.
     * rewrite <- (HDSV(N(length values)+i)x(coding_lt_add_left M(N(length values))i count Hi)).
       apply HASV;exact Hi.
     * assert(Hbound:coding_lt M(N(length values)+i)(S(N(length values)+count))).
       { rewrite <-prefix_add_succ_right. apply coding_lt_add_left;exact Hi. }
       rewrite <- (HDSW(N(length values)+i)x Hbound).
       apply HASW;exact Hi.
Qed.
End Prefix.
Print Assumptions machine230_chain_prepend.
Print Assumptions machine230_finite_prefix_chain.
