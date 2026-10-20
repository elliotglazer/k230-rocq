(** Compose two explicit extensions by finite closed ZFR backgrounds. *)
From PAModel Require Import Model FiniteCoding NumericalContexts ContextCombination SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_native_closed_extensions M gb gc gn ab ac an xb xc xn bb bc bn yb yc yn:
 source_zfr_context M ab ac an->context_union M gb gc gn ab ac an xb xc xn->
 source_zfr_context M bb bc bn->context_union M xb xc xn bb bc bn yb yc yn->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 context_included M yb yc yn ub uc un.
Proof.
 intros HA HX HB HY.
 destruct(context_union_total M ab ac an bb bc bn)as(nb&nc&nn&HN).
 assert(HNC:source_zfr_context M nb nc nn).
 { intros a HE. apply(proj1(proj2 HN a))in HE. destruct HE as[HE|HE];[exact(HA a HE)|exact(HB a HE)]. }
 destruct(context_union_total M gb gc gn nb nc nn)as(ub&uc&un&HU).
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|].
 intros a HE. apply(proj1(proj2 HY a))in HE. apply(proj2(proj2 HU a)). destruct HE as[HE|HE].
 - apply(proj1(proj2 HX a))in HE. destruct HE as[HE|HE];[now left|right;apply(proj2(proj2 HN a));now left].
 - right. apply(proj2(proj2 HN a)). now right.
Qed.
Print Assumptions source_native_closed_extensions.
