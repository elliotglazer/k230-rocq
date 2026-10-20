(** Constructive suffix retailing for arbitrary internally coded register lists. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking
 TM230UnaryBlocks TM230CarryChainSyntax TM230ChainRetailingSyntax.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Retail.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S O).
Local Infix "+":=(addM M).
Add Ring machine230_retail_ring:(model_semiring M).
Theorem machine230_carry_chain_retail_uniform vb vc:forall count,
 machine230_carry_chain_retail_at M vb vc count.
Proof.
 apply(definable_induction M(machine230_carry_chain_retail_at M vb vc)
  (machine230_carry_chain_retail_definable M vb vc)).
 -intros start tail. exists tail,tail,tail. split;[apply beta_singleton|].
  split;[apply beta_singleton|]. intros i Hi;exfalso;exact(coding_not_lt_zero M i Hi).
 -intros n IH start tail.
  destruct(IH(S start)tail)as[wb[wc[oldfirst[Hfirst[Htail HC]]]]].
  destruct(beta_total M vb vc start)as[v Hv].
  destruct(machine230_unary_block_total M v oldfirst)as[first HB].
  destruct(beta_concatenate M first first one wb wc(S n))as[db[dc[HD HT]]].
  assert(Hhead:beta M db dc O first).
  {apply HD;[apply coding_zero_lt_succ|apply beta_singleton]. }
  assert(Hshift:forall i x,coding_lt M i(S n)->beta M wb wc i x->beta M db dc(S i)x).
  {intros i x Hi Hx. pose proof(HT i x Hi Hx)as H.
   rewrite(Arithmetic.add_succ M O i),(Arithmetic.add_zero M i)in H. exact H. }
  exists db,dc,first. split;[exact Hhead|]. split.
  +exact(Hshift n tail(coding_lt_succ M n)Htail).
  +intros i Hi. destruct(@Peano.zero_or_succ D(raw_interpretation M)
   (fun ax H rho=>axioms M ax rho H)i)as[Ei|[j Ei]];subst i.
   *exists v,first,oldfirst. split.
    --change(beta M vb vc(start+O)v). replace(start+O)with start by(rewrite Arithmetic.add_comm,Arithmetic.add_zero;reflexivity). exact Hv.
    --split;[exact Hhead|]. split;[exact(Hshift O oldfirst(coding_zero_lt_succ M n)Hfirst)|exact HB].
   *assert(Hj:coding_lt M j n)by(now apply coding_lt_succ_cancel).
    destruct(HC j Hj)as[vj[x[y[Hvj[Hx[Hy Hblock]]]]]].
    exists vj,x,y. split.
    --change(beta M vb vc(start+S j)vj). replace(start+S j)with(S start+j).
      ++exact Hvj.
      ++rewrite(Arithmetic.add_succ M start j),(succ_as_add M j),(succ_as_add M(start+j)). ring.
    --split;[exact(Hshift j x(proj2(coding_lt_succ_cases M j n)(or_introl Hj))Hx)|].
      split;[apply Hshift;[now apply coding_lt_succ_cancel|exact Hy]|exact Hblock].
Qed.
Theorem machine230_carry_chain_retail_total vb vc count tail:
 exists wb wc first,machine230_carry_chain M vb vc wb wc count /\
 beta M wb wc O first /\beta M wb wc count tail.
Proof.
 destruct(machine230_carry_chain_retail_uniform vb vc count O tail)as[wb[wc[first[HF[HT HC]]]]].
 exists wb,wc,first. split;[|auto]. intros i Hi.
 destruct(HC i Hi)as[v[x[y[Hv[Hx[Hy HB]]]]]].
 exists v,x,y. rewrite Arithmetic.add_zero in Hv. auto.
Qed.
End Retail.
Print Assumptions machine230_carry_chain_retail_uniform.
Print Assumptions machine230_carry_chain_retail_total.
