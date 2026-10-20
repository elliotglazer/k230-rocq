(** The fixed named App, successor and agreement relations used by the
    varying-matrix recursion proof, in the same pinned source syntax. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceParameterTransport.
From OldZF Require Std_setbase Std_setinf Std_setrec.
From OldZFC Require Z_rel.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_rec_app_predicate :sf_form:=isolated_formula(OldZF.Std_setbase.App
  (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition source_rec_successor_predicate :sf_form:=isolated_formula(OldZF.Std_setinf.phSig).
Definition source_rec_agreement_predicate :sf_form:=isolated_formula(OldZF.Std_setrec.Agr
  (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition source_rec_env3 {A:Type}(a b c:A)(i:nat):=match i with 0=>a|1=>b|_=>c end.
Definition source_rec_env2 {A:Type}(a b:A)(i:nat):=match i with 0=>a|_=>b end.
Definition source_rec_app M f u v out:=code_relation M(source_rec_env3 f u v)
  (source_parameter_expression(source_finite_parameter_names 3)source_rec_app_predicate)out.
Definition source_rec_successor M u v out:=code_relation M(source_rec_env2 u v)
  (source_parameter_expression(source_finite_parameter_names 2)source_rec_successor_predicate)out.
Definition source_rec_agreement M f g z out:=code_relation M(source_rec_env3 f g z)
  (source_parameter_expression(source_finite_parameter_names 3)source_rec_agreement_predicate)out.

Lemma source_rec_app_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 3 source_rec_app_predicate.
Proof.
  apply(@isolated_bounded OC.falsity_on 3(OldZF.Std_setbase.App(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))).
  apply OldZFC.Z_rel.fb_bounded. OldZF.Std_setrec.fbsolve.
Qed.
Lemma source_rec_successor_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 2 source_rec_successor_predicate.
Proof.
  apply(@isolated_bounded OC.falsity_on 2 OldZF.Std_setinf.phSig).
  apply OldZFC.Z_rel.fb_bounded. unfold OldZF.Std_setinf.phSig,OldUndecidability.FOL.Sets.minZF.is_sigma. cbn. repeat split;lia.
Qed.
Lemma source_rec_agreement_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 3 source_rec_agreement_predicate.
Proof.
  apply(@isolated_bounded OC.falsity_on 3(OldZF.Std_setrec.Agr(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))).
  apply OldZFC.Z_rel.fb_bounded. OldZF.Std_setrec.fbsolve.
Qed.

Theorem source_rec_app_total M f u v:exists out,source_rec_app M f u v out.
Proof. apply code_relation_total. Qed.
Theorem source_rec_successor_total M u v:exists out,source_rec_successor M u v out.
Proof. apply code_relation_total. Qed.
Theorem source_rec_agreement_total M f g z:exists out,source_rec_agreement M f g z out.
Proof. apply code_relation_total. Qed.

Theorem source_rec_app_bounded M f u v out k:coding_lt M f k ->coding_lt M u k ->coding_lt M v k ->
  source_rec_app M f u v out ->source_bounded M out k.
Proof.
  intros HF HU HV HO. apply(source_parameter_graph_bounded M 3 source_rec_app_predicate source_rec_app_finite_bound
    (source_finite_parameter_names 3)(source_rec_env3 f u v)k);[|exact HO].
  intros[|[|[|i]]] x HI HX;try lia.
  - change(x=f)in HX. now subst x.
  - change(x=u)in HX. now subst x.
  - change(x=v)in HX. now subst x.
Qed.
Theorem source_rec_successor_bounded M u v out k:coding_lt M u k ->coding_lt M v k ->
  source_rec_successor M u v out ->source_bounded M out k.
Proof.
  intros HU HV HO. apply(source_parameter_graph_bounded M 2 source_rec_successor_predicate source_rec_successor_finite_bound
    (source_finite_parameter_names 2)(source_rec_env2 u v)k);[|exact HO].
  intros[|[|i]] x HI HX;try lia.
  - change(x=u)in HX. now subst x.
  - change(x=v)in HX. now subst x.
Qed.

Print Assumptions source_rec_app_finite_bound.
Print Assumptions source_rec_successor_finite_bound.
Print Assumptions source_rec_agreement_finite_bound.
Print Assumptions source_rec_app_total.
Print Assumptions source_rec_successor_total.
Print Assumptions source_rec_agreement_total.
Print Assumptions source_rec_app_bounded.
Print Assumptions source_rec_successor_bounded.
