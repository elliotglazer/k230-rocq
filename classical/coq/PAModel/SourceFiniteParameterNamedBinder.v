(** Finite parameter compilation agrees with an actual named binder.
    Parameter values and the fresh binder are arbitrary PA-model names. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceParameterRenamingTransport
 RawBinderRenaming NumericalRenamingMaps NumericalRenaming SourceNamedQuantifierRules SchemaConstructorBounds.
From Undecidability.FOL Require Import Syntax.Bounded.
From Stdlib Require Import Lia Arith.PeanoNat.
Unset Implicit Arguments.

Definition finite_binder_environment {A}(r:A)(rho:nat->A)i:=match i with 0=>r|S j=>rho j end.
Lemma finite_parameter_name_graph M n rho i:(i<n)%nat ->
 code_relation M rho(source_finite_parameter_names n i)(rho i).
Proof.
 intro HI. unfold source_finite_parameter_names.
 assert(E:Nat.ltb i n=true)by(now apply Nat.ltb_lt). rewrite E. reflexivity.
Qed.

Theorem source_finite_parameter_named_binder_body M n(phi:sf_form)rho r body closed rb rc:
 bounded(S n)phi ->(forall i,(i<n)%nat ->r<>rho i) ->raw_binder_renaming M r rb rc ->
 code_relation M(finite_binder_environment r rho)(source_parameter_expression(source_finite_parameter_names(S n))phi)body ->
 code_relation M rho(source_parameter_expression(source_parameter_up(source_finite_parameter_names n))phi)closed ->
 numerical_renaming M body rb rc(succM M r)(code_numeral M 1)closed.
Proof.
 intros HB HFresh HMap HBody HClosed.
 set(target:=finite_binder_environment(zeroM M)(fun i=>succM M(rho i))).
 assert(HExt:forall i x,(i<S n)%nat ->
  (code_relation M rho(source_parameter_up(source_finite_parameter_names n)i)x <->
   code_relation M target(source_finite_parameter_names(S n)i)x)).
 { intros[|i]x HI.
   - assert(HA:code_relation M rho(source_parameter_up(source_finite_parameter_names n)0)(zeroM M))by reflexivity.
     pose proof(finite_parameter_name_graph M(S n)target 0 ltac:(lia))as HB'.
     change(code_relation M target(source_finite_parameter_names(S n)0)(zeroM M))in HB'.
     split;intro HX.
     + pose proof(code_relation_functional M _ rho x(zeroM M)HX HA)as E. now subst x.
     + pose proof(code_relation_functional M _ target x(zeroM M)HX HB')as E. now subst x.
   - assert(HA:code_relation M rho(source_parameter_up(source_finite_parameter_names n)(S i))(succM M(rho i))).
     { exists(rho i),(code_numeral M 1). split;[apply finite_parameter_name_graph;lia|].
       split;[reflexivity|apply Arithmetic.succ_as_add]. }
     pose proof(finite_parameter_name_graph M(S n)target(S i)HI)as HB'.
     change(code_relation M target(source_finite_parameter_names(S n)(S i))(succM M(rho i)))in HB'.
     split;intro HX.
     + pose proof(code_relation_functional M _ rho x(succM M(rho i))HX HA)as E. now subst x.
     + pose proof(code_relation_functional M _ target x(succM M(rho i))HX HB')as E. now subst x. }
 pose proof(proj1(source_parameter_graph_ext M(S n)phi HB(source_parameter_up(source_finite_parameter_names n))
  (source_finite_parameter_names(S n))rho target HExt closed)HClosed)as HTarget.
 apply(source_parameter_renaming_transport M(S n)phi HB(source_finite_parameter_names(S n))(source_finite_parameter_names(S n))
  (finite_binder_environment r rho)target rb rc(succM M r)(code_numeral M 1)body closed);[|exact HBody|exact HTarget].
 intros[|i]x y HI HX HY.
 - pose proof(finite_parameter_name_graph M(S n)(finite_binder_environment r rho)0 HI)as HGX.
   pose proof(finite_parameter_name_graph M(S n)target 0 HI)as HGY.
   pose proof(code_relation_functional M _ _ x r HX HGX)as E. subst x.
   pose proof(code_relation_functional M _ _ y(zeroM M)HY HGY)as E. subst y.
   apply(proj2(HMap r(zeroM M))). now left.
 - pose proof(finite_parameter_name_graph M(S n)(finite_binder_environment r rho)(S i)HI)as HGX.
   pose proof(finite_parameter_name_graph M(S n)target(S i)HI)as HGY.
   pose proof(code_relation_functional M _ _ x(rho i)HX HGX)as E. subst x.
   pose proof(code_relation_functional M _ _ y(succM M(rho i))HY HGY)as E. subst y.
   apply(proj2(HMap(rho i)(succM M(rho i)))). right. split;[|reflexivity].
   intro E. exact(HFresh i ltac:(lia)(eq_sym E)).
Qed.

Theorem source_finite_parameter_named_binder M n(phi:sf_form)rho r body out(universal:bool):
 bounded(S n)phi ->(forall i,(i<n)%nat ->r<>rho i) ->
 code_relation M(finite_binder_environment r rho)(source_parameter_expression(source_finite_parameter_names(S n))phi)body ->
 code_relation M rho(E_sf(if universal then SFAll else SFEx)
  (source_parameter_expression(source_parameter_up(source_finite_parameter_names n))phi)(CEconst 0))out ->
 source_named_quantifier M universal r body out.
Proof.
 intros HB HF HBody HOut.
 destruct(code_relation_total M(source_parameter_expression(source_parameter_up(source_finite_parameter_names n))phi)rho)as(closed&HClosed).
 pose proof(proj1(schema_expression_graph M rho(if universal then SFAll else SFEx)_ (CEconst 0)
  closed(zeroM M)out HClosed eq_refl)HOut)as HQ.
 destruct(raw_binder_renaming_total M r)as(rb&rc&HMap).
 exists rb,rc,closed. split;[exact HMap|]. split;[|exact HQ].
 exact(source_finite_parameter_named_binder_body M n phi rho r body closed rb rc HB HF HMap HBody HClosed).
Qed.
Print Assumptions source_finite_parameter_named_binder_body.
Print Assumptions source_finite_parameter_named_binder.
