(** Actual carry through an internally long suffix, the six blank-tail steps,
    and ordinary RETURN with a newly appended spare block. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230Paths TM230ExactPaths TM230RegisterPrefix
 TM230CarryChainSyntax TM230CarryPrefixes TM230ViewRuns TM230CarryRollbackIteration
 TM230ReturnPrefixes TM230ReturnIteration TM230PrefixAlignment TM230ChainRetailing TM230BlankIncrement.
Unset Implicit Arguments.
Theorem machine230_increment_internal_suffix M vb vc wb wc count left first s:
 machine230_carry_chain M vb vc wb wc count ->beta M wb wc(zeroM M)first ->
 beta M wb wc count(zeroM M) ->machine230_right_view M 0 left first s ->
 exists ob oc output t,machine230_carry_chain M vb vc ob oc count /\
 beta M ob oc(zeroM M)output /\beta M ob oc count(code_numeral M 6) /\
 machine230_left_view M 40 output(machine230_inserted_prefix_value M left)t /\
 machine230_reaches M s t.
Proof.
 intros HC Hfirst Hlast Hs.
 destruct(machine230_carry_rollback_total M vb vc wb wc count left first(zeroM M)HC Hfirst Hlast)
  as[lb[lc[final[H0[Hfinal[HL[HF HR]]]]]]].
 destruct(machine230_bounded_view_from M false 0 count left first final(zeroM M)s HF Hs)
  as[mid[time[slack[Hmid[Htime Hpath]]]]].
 destruct(machine230_increment_blank_tail M final mid Hmid)as[next[Hnext Hblank]].
 destruct(machine230_carry_to_return_endpoints M vb vc lb lc count left final HL H0 Hfinal)
  as[rb[rc[Hreturn[Hr0 Hrn]]]].
 destruct(machine230_carry_chain_retail_total M vb vc count(code_numeral M 6))
  as[ob[oc[output[HO[HO0 HOn]]]]].
 change(machine230_left_view M 40(code_numeral M 6)(machine230_inserted_prefix_value M final)next)in Hnext.
 destruct(machine230_return_from M vb vc ob oc rb rc count
  (machine230_inserted_prefix_value M left)(machine230_inserted_prefix_value M final)
  output(code_numeral M 6)next HO Hreturn Hr0 Hrn HO0 HOn Hnext)
  as[t[returntime[returnslack[Ht[Hreturntime Hreturnpath]]]]].
 exists ob,oc,output,t. split;[exact HO|]. split;[exact HO0|]. split;[exact HOn|]. split;[exact Ht|].
 eapply machine230_reaches_trans;[eapply machine230_reaches_in_forget;exact Hpath|].
 eapply machine230_reaches_trans;[eapply machine230_reaches_in_forget;exact Hblank|].
 eapply machine230_reaches_in_forget;exact Hreturnpath.
Qed.
Print Assumptions machine230_increment_internal_suffix.
