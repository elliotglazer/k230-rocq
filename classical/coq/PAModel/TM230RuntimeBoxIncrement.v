(** Exact increment oracle with decoded physical suffix and one appended spare. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 PowerTwoSyntax PowerTwoRecurrence TM230UnaryBlocks TM230RegisterWords TM230RegisterPrefix
 TM230CarryChainSyntax TM230SpareSyntax TM230SpareRecurrence TM230SparePower TM230SpareBlocks TM230SpareChains
 TM230RuntimeBox TM230RuntimeBoxProperties TM230RuntimeBoxSimplePaths
 TM230FinitePrefixChain TM230FiniteChainDecode TM230BoxIncrement TM230BitArithmetic TM230LeftView TM230Paths.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Section Increment.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring runtime_box_increment_ring:(model_semiring M).
Lemma machine230_blocks_list_at values tail word:
 machine230_blocks_list M values tail word <->
 machine230_blocks_at M(length values)(fun idx=>nth idx values Z)tail word.
Proof.
 induction values as[|v values IH]in word|-*;cbn[machine230_blocks_list machine230_blocks_at length nth].
 -reflexivity.
 -split;intros[inside[HI HV]];exists inside;split;[now apply IH|exact HV|now apply IH|exact HV].
Qed.
Theorem machine230_runtime_increment_path values E r left word s:
 (r<9)%nat->machine230_runtime_box M values E(Runtime230.BMark r)word->
 machine230_right_view M 64 left word s->
 exists output t,machine230_runtime_box M values E(Runtime230.BPlain(Runtime230.FInc r))output /\
 machine230_left_view M 40 output left t /\machine230_reaches M s t.
Proof.
 intros HR[HL[HE[spare[HS HW]]]]HV.
 destruct(nth_error values r)as[v|]eqn:HN;[|apply nth_error_None in HN;lia].
 destruct(machine230_marked_blocks_split M values r v spare word HN HW)as[inside[target[HI[HT HP]]]].
 destruct(power2_total M(N 3*E))as[p Hpower].
 destruct(machine230_spare_chain_tables M E)as[vb[vc[Hones Htables]]].
 destruct(Htables spare p HS Hpower Z)as[wb[wc[HC[HF Hlast]]]].
 replace(spare+p*Z)with spare in HF by ring.
 pose proof(proj1(machine230_blocks_list_at(skipn(S r)values)spare inside)HI)as HIat.
 destruct(machine230_finite_prefix_chain M(skipn(S r)values)vb vc wb wc E spare Z inside HC HF Hlast HIat)
 as[dv[ev[dw[ew[HD[HDfirst[HDlast[HDprefix[HDsuffix HDwords]]]]]]]]].
 destruct(machine230_box_increment M(firstn r values)v left inside target word dv ev dw ew
 (N(length(skipn(S r)values))+E)s HT HP HD HDfirst HDlast HV)
 as[ob[oc[tailOutput[target'[output[t[HO[HO0[HOn[HT'[HP'[HTview Hpath]]]]]]]]]]]].
 destruct(machine230_finite_prefix_suffix_decode M(skipn(S r)values)dv ev vb vc ob oc E tailOutput(N 6)
 HO HDprefix HDsuffix HO0 HOn)
 as[newSpare[nb[nc[HsuffixBlocks[HsuffixChain[HsuffixFirst HsuffixLast]]]]]].
 pose proof(machine230_spare_chain_first M vb vc nb nc E(N 6)newSpare spare p
 Hones HsuffixChain HsuffixLast HsuffixFirst HS Hpower)as EnewSpare.
 assert(HnewSpare:machine230_spare M(succM M E)newSpare).
 {rewrite EnewSpare. replace(spare+p*N 6)with(spare+N 6*p)by ring.
  exact(machine230_spare_append M E spare p HS Hpower). }
 exists output,t. split.
 -split;[exact HL|]. split;[exact HE|].
  exists(machine230_update_values r(succM M v)values),newSpare. split.
  +exists v;auto.
  +split;[exact HnewSpare|].
   exact(machine230_blocks_list_update M values r v(succM M v)newSpare tailOutput target' output HN HsuffixBlocks HT' HP').
 -auto.
Qed.
End Increment.
Print Assumptions machine230_runtime_increment_path.