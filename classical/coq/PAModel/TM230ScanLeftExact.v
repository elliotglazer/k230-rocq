(** A PA-definable homogeneous left scan of arbitrary internal length. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 TM230LiteralActions TM230TransitionArithmetic TM230BinaryStep TM230Paths TM230ExactPaths TM230BitArithmetic TM230LeftView
 PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_left_exact_bit_formula(t:term):form:=t==zero ∨t==num 1.
Lemma machine230_left_exact_bit_formula_correct M rho t:
 holds M rho(machine230_left_exact_bit_formula t)<->machine230_is_bit M(evalM M rho t).
Proof. unfold machine230_left_exact_bit_formula,machine230_is_bit. rewrite holds_or. reflexivity. Qed.
Definition machine230_left_scan_exact_property M q b w n:=
 forall p k r h l h' l',power2 M n p ->p=succM M k ->
 machine230_is_bit M h ->machine230_is_bit M h' ->
 addM M h(mulM M(code_numeral M 2)l)=
 addM M(mulM M k(machine230_bitM M b))
 (mulM M p(addM M h'(mulM M(code_numeral M 2)l'))) ->
 machine230_reaches_in M n
 (machine230_mk_config(carrier M)(code_numeral M q)l h r)
 (machine230_mk_config(carrier M)(code_numeral M q)l' h'
 (addM M(mulM M p r)(mulM M k(machine230_bitM M w)))).
Definition machine230_left_scan_exact_formula q b w:form:=
 ∀∀∀∀∀∀∀(power2_formula $7 $6 →$6==σ $5 →
 machine230_left_exact_bit_formula $3 →machine230_left_exact_bit_formula $1 →
 ($3 ⊕num 2⊗$2)==($5⊗num(machine230_bit b) ⊕$6⊗($1⊕num 2⊗$0)) →
 machine230_reaches_in_formula $7(num q)$2 $3 $4(num q)$0 $1
 ($6⊗$4⊕$5⊗num(machine230_bit w))).
Local Opaque holds power2_formula machine230_reaches_in_formula.
Lemma machine230_left_scan_exact_definable M q b w:
 Definable1 M(machine230_left_scan_exact_property M q b w).
Proof.
 exists(machine230_left_scan_exact_formula q b w),(fun _=>zeroM M). intro n.
 unfold machine230_left_scan_exact_formula,machine230_left_scan_exact_property.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite power2_formula_correct. setoid_rewrite machine230_left_exact_bit_formula_correct.
 setoid_rewrite machine230_reaches_in_formula_correct.
 setoid_rewrite machine230_holds_equal.
 repeat setoid_rewrite machine230_eval_add. repeat setoid_rewrite machine230_eval_mul.
 repeat setoid_rewrite code_eval_num. reflexivity.
Qed.
Section Scan.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation one := (S Z).
Local Notation two := (S one).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring machine230_left_scan_exact_ring : (model_semiring M).
Theorem machine230_scan_left_exact q b w:
 Public230.tmn q b=Some(w,TM.L,q) ->forall n,machine230_left_scan_exact_property M q b w n.
Proof.
 intro Htable. apply(definable_induction M(machine230_left_scan_exact_property M q b w)
 (machine230_left_scan_exact_definable M q b w)).
 -intros p k r h l h' l' Hp Hpk Hh Hh' E.
  pose proof(power2_zero_value M p Hp)as Ep.
  assert(Ek:k=Z)by(apply(succ_injective M);now rewrite <-Hpk,Ep).
  subst p k. change(h+two*l=Z*machine230_bitM M b+one*(h'+two*l'))in E.
  assert(Ewords:two*l+h=two*l'+h').
  {eapply eq_trans;[replace(two*l+h)with(h+two*l)by ring;exact E|]. rewrite(succ_as_add M Z);ring. }
  destruct(machine230_pop_unique M h l h' l' Hh Hh' Ewords)as[Eh El]. subst h' l'.
  replace(one*r+Z*machine230_bitM M w)with r by(rewrite succ_as_add;ring).
  apply machine230_reaches_in_zero.
 -intros n IH p k r h l h' l' Hp Hpk Hh Hh' E.
  destruct(power2_successor_inv M n p Hp)as[p0[Hp0 Ep]]. change(p=two*p0)in Ep.
  destruct(power2_positive_successor M n p0 Hp0)as[k0 Hk0].
  assert(Ek:k=S(two*k0)).
  {apply(succ_injective M). rewrite <-Hpk,Ep,Hk0. try rewrite(succ_as_add M k0);try rewrite(succ_as_add M(S(two*k0)));try rewrite(succ_as_add M(two*k0));try rewrite(succ_as_add M one). ring. }
  change(h+two*l=k*machine230_bitM M b+p*(h'+two*l'))in E.
  set(tail:=h'+two*l'). set(midword:=k0*machine230_bitM M b+p0*tail).
  set(midright:=two*r+machine230_bitM M w).
  destruct(machine230_pop_total M midword)as[hm[lm[Hhm Emid]]].
  set(smid:=machine230_mk_config D(code_numeral M q)lm hm midright).
  assert(Einput:h+two*l=machine230_bitM M b+two*midword).
  {eapply eq_trans;[exact E|]. unfold midword,tail. rewrite Ep,Ek,Hk0. try rewrite(succ_as_add M k0);try rewrite(succ_as_add M(S(two*k0)));try rewrite(succ_as_add M(two*k0));try rewrite(succ_as_add M one). ring. }
  assert(Hfirst:machine230_step M(machine230_mk_config D(code_numeral M q)l h r)smid).
  {apply(machine230_left_view_step M q b w q r midword _ _ Htable).
   -unfold machine230_left_view;cbn[machine230_state machine230_left machine230_head machine230_right].
    split;[reflexivity|]. split;[reflexivity|]. split;[exact Hh|]. eapply eq_trans;[exact(eq_sym Einput)|ring].
   -unfold machine230_left_view,smid,midright;cbn[machine230_state machine230_left machine230_head machine230_right].
    split;[reflexivity|]. split;[reflexivity|]. split;[exact Hhm|exact Emid]. }
  assert(Eremaining:hm+two*lm=k0*machine230_bitM M b+p0*(h'+two*l')).
  {unfold midword,tail in Emid. eapply eq_trans;[|exact(eq_sym Emid)]. ring. }
  pose proof(IH p0 k0 midright hm lm h' l' Hp0 Hk0 Hhm Hh' Eremaining)as Hrest.
  assert(Eright:p0*midright+k0*machine230_bitM M w=p*r+k*machine230_bitM M w).
  {unfold midright. rewrite Ep,Ek,Hk0. try rewrite(succ_as_add M k0);try rewrite(succ_as_add M(S(two*k0)));try rewrite(succ_as_add M(two*k0));try rewrite(succ_as_add M one). ring. }
  rewrite Eright in Hrest.
  exact(machine230_reaches_in_step M _ smid _ n Hfirst Hrest).
Qed.
End Scan.
Print Assumptions machine230_left_scan_exact_definable.
Print Assumptions machine230_scan_left_exact.
