(** Actual normal search-cycle realization, with only the pending AX action explicit. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SearchStep
 Program230Configurations Program230Histories Program230InstructionFormula Program230RootReady
 Program230AXContract Program230SearchState Program230SearchPrefix Program230SearchRealization
 Program230SearchActionFacts Program230SearchMP Program230SearchDropNip Program230SearchAX.
Unset Implicit Arguments.
Theorem p230_search_kernel_history M:
 p230_ax_action_contract M->forall s t pl np ac d,
 search_kernel_relation M s t pl np ac d->
 p230_search_action_realizes M(p230_search_prefix_configuration M s np ac pl d)t.
Proof.
 intros HX s t pl np ac d HK.
 destruct HK as[[Hac[Hcommon[Hh Hmp]]]|[[Hac[Hcommon[Htw[Hpair Hh]]]]|[[Hac[Hneq[Hcommon[Htw Hpair]]]]|HXK]]].
 -subst ac;exact(p230_search_mp_kernel M s t pl np d Hcommon Hh Hmp).
 -subst ac;exact(p230_search_drop_kernel M s t pl np d Hcommon Htw Hpair Hh).
 -subst ac;exact(p230_search_nip_kernel M s t pl np d Hneq Hcommon Htw Hpair).
 -destruct HXK as[code[y[pl4[u[pl5[bound[Hac[Hy[Hu[Hb[Hpl[Hnp[Hd[Hh[Hstack Hgate]]]]]]]]]]]]]]].
  exact(p230_search_ax_kernel M HX s t pl np ac d code y pl4 u pl5 bound Hac Hy Hu Hb Hpl Hnp Hd Hh Hstack Hgate).
Qed.
Theorem p230_normal_search_from_ax M:p230_ax_action_contract M->p230_normal_search_macro M.
Proof.
 intros HX s t pc Hpc[pl1[np[ac[pl2[x[pl3[d[HP HK]]]]]]]].
 destruct(p230_search_prefix_history M s pc pl1 np ac pl2 x pl3 d Hpc HP)as[b[c[time[HR[HT Hpos]]]]].
 exact(p230_search_action_prepend M _ _ t b c time HR HT(p230_search_kernel_history M HX s t pl3 np ac d HK)).
Qed.
Print Assumptions p230_search_kernel_history.
Print Assumptions p230_normal_search_from_ax.
