(** Finite parameter compilation avoids any name avoided by every parameter
    image. The proof constructs a genuine finite numerical renaming and uses
    image vacuity, including under arbitrary nested finite source binders. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 SetFormulaCodes FixedSourceBounds SourceBounded SourceNumeralLift NumericalEnvironments
 NumericalRenamingMaps NumericalRenaming SourceFiniteParameters SourceFiniteNameParameters
 SourceParameterGraphs SourceNamedVacuity SourceNamedVacuityImages.
From FOL Require Import FullSyntax.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Arith.PeanoNat Lia.
Unset Implicit Arguments.

Theorem source_finite_parameter_graph_map_total M count :forall names rho delta,
 exists b c,forall i x,(i<count)%nat ->code_relation M rho(names i)x ->
 renaming_lookup M b c(code_numeral M count)delta(code_numeral M i)x.
Proof.
 induction count as[|count IH];intros names rho delta.
 - exists(zeroM M),(zeroM M). intros i x HI. lia.
 - destruct(IH(fun i=>names(S i))rho delta)as(b&c&HMap).
   destruct(code_relation_total M(names 0)rho)as(head&HHead).
   destruct(environment_cons_total M b c(code_numeral M count)head)as(d&e&n&HCons).
   assert(EN:n=code_numeral M(S count))by exact(proj1 HCons). subst n.
   exists d,e. intros[|i]x HI HX.
   + assert(E:x=head)by exact(code_relation_functional M(names 0)rho x head HX HHead). subst x.
     apply(proj2(renaming_lookup_inside M d e(code_numeral M(S count))delta
       (zeroM M)head(coding_zero_lt_succ M(code_numeral M count)))).
     apply(proj1(environment_lookup_inside M d e(code_numeral M(S count))(zeroM M)head
       (coding_zero_lt_succ M(code_numeral M count)))). exact(proj1(proj2 HCons)).
   + assert(HI':(i<count)%nat)by lia.
     pose proof(proj2(fixed_source_numeral_lt_iff M i count)HI')as HOldLt.
     pose proof(proj2(fixed_source_numeral_lt_iff M(S i)(S count))HI)as HNewLt.
     apply(proj2(renaming_lookup_inside M d e _ delta _ _ HNewLt)).
     apply(proj1(environment_lookup_inside M d e _ _ _ HNewLt)).
     apply(proj2(proj2 HCons)).
     apply(proj2(environment_lookup_inside M b c _ _ _ HOldLt)).
     exact(proj1(renaming_lookup_inside M b c _ delta _ _ HOldLt)(HMap i x HI' HX)).
Qed.

Theorem source_bounded_parameter_renaming {ff} M bound
 (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff):
 bounded bound phi ->forall names rho out,
 code_relation M rho(source_parameter_expression names phi)out ->
 exists b c,numerical_renaming M(code_numeral M(sf_encode phi))b c(code_numeral M bound)(zeroM M)out /\
 (forall i x,(i<bound)%nat ->code_relation M rho(names i)x ->
  renaming_lookup M b c(code_numeral M bound)(zeroM M)(code_numeral M i)x).
Proof.
 intros HB names rho out HO.
 destruct(source_finite_parameter_graph_map_total M bound names rho(zeroM M))as(b&c&HMap).
 exists b,c. split;[|exact HMap].
 set(padded:=fun i=>if Nat.ltb i bound then names i else CEconst i).
 assert(HP:code_relation M rho(source_parameter_expression padded phi)out).
 { apply(proj1(source_parameter_graph_ext M bound phi HB names padded rho rho
     ltac:(intros i x HI;unfold padded;destruct(Nat.ltb_spec i bound);[reflexivity|lia])out)).
   exact HO. }
 apply(source_finite_parameter_renaming M phi padded rho b c(code_numeral M bound)(zeroM M)out);[|exact HP].
 intros i x HX. unfold padded in HX. destruct(Nat.ltb_spec i bound)as[HI|HI].
 - exact(HMap i x HI HX).
 - change(x=code_numeral M i)in HX. subst x.
   apply(proj2(renaming_lookup_outside M b c(code_numeral M bound)(zeroM M)
     (code_numeral M i)(code_numeral M i)
     ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M i bound))in H;lia))).
   symmetry. apply coding_add_zero_r.
Qed.

Theorem source_parameter_graph_named_vacuous {ff} M bound
 (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff):
 bounded bound phi ->forall names rho x,
 (forall i y,(i<bound)%nat ->code_relation M rho(names i)y ->y<>x) ->
 forall out,code_relation M rho(source_parameter_expression names phi)out ->source_named_vacuous M x out.
Proof.
 intros HB names rho x HFresh out HO.
 destruct(source_bounded_parameter_renaming M bound phi HB names rho out HO)as(b&c&HR&HMap).
 apply(source_named_vacuous_renaming_image M(code_numeral M(sf_encode phi))out(code_numeral M bound)
   b c(code_numeral M bound)(zeroM M)x(proj2(source_formula_numeral_bounded M phi bound)HB)HR).
 intros i j HI HJ. destruct(source_numeral_initial_segment M bound i HI)as(index&HIndex&->).
 destruct(code_relation_total M(names index)rho)as(value&HValue).
 assert(E:j=value)by exact(renaming_lookup_functional M b c(code_numeral M bound)(zeroM M)
   (code_numeral M index)j value HJ(HMap index value HIndex HValue)).
 subst j. exact(HFresh index value HIndex HValue).
Qed.

Print Assumptions source_finite_parameter_graph_map_total.
Print Assumptions source_bounded_parameter_renaming.
Print Assumptions source_parameter_graph_named_vacuous.
