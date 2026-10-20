(** Exact binary length and append behavior of the spare-register tail. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 PowerTwoSyntax PowerTwoRecurrence TM230SpareSyntax TM230SpareRecurrence.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_spare_power_property M n:=forall word p,
 machine230_spare M n word->power2 M(mulM M(code_numeral M 3)n)p->
 addM M(mulM M(code_numeral M 7)word)(code_numeral M 6)=
 mulM M(code_numeral M 6)p.
Local Opaque holds machine230_spare_formula power2_formula.
Lemma machine230_spare_power_definable M:
 Definable1 M(machine230_spare_power_property M).
Proof.
 exists(∀∀(machine230_spare_formula $2 $1→power2_formula(num 3⊗$2)$0→
   (num 7⊗$1⊕num 6)==(num 6⊗$0))),(fun _=>zeroM M).
 intro n. unfold machine230_spare_power_property.
 rewrite holds_all. setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite machine230_spare_formula_correct. setoid_rewrite power2_formula_correct.
 setoid_rewrite spare_holds_equal. reflexivity.
Qed.
Section Power.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation N := (code_numeral M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring spare_power_ring:(model_semiring M).
Ltac spare_constants := cbn[code_numeral];repeat multimatch goal with
 | |- context[succM M ?x]=>lazymatch x with
   | zeroM _=>fail 0
   | _=>rewrite(succ_as_add M x)
   end
 end.
Lemma spare_exponent_step n:N 3*S n=S(S(S(N 3*n))).
Proof.
 rewrite(succ_as_add M n),(succ_as_add M(S(S(N 3*n)))),
   (succ_as_add M(S(N 3*n))),(succ_as_add M(N 3*n)).
 spare_constants;ring.
Qed.
Lemma spare_power_step n p:power2 M(N 3*n)p->power2 M(N 3*S n)(N 8*p).
Proof.
 intro H. rewrite spare_exponent_step.
 replace(N 8*p)with(N 2*(N 2*(N 2*p)))by(spare_constants;ring).
 apply power2_successor,power2_successor,power2_successor,H.
Qed.
Theorem machine230_spare_power:forall n word p,
 machine230_spare M n word->power2 M(N 3*n)p->N 7*word+N 6=N 6*p.
Proof.
 apply(definable_induction M(machine230_spare_power_property M)
   (machine230_spare_power_definable M)).
 - intros word p Hword Hp. rewrite(machine230_spare_zero_value M word Hword).
   replace(N 3*Z)with Z in Hp by ring. rewrite(power2_zero_value M p Hp).
   spare_constants;ring.
 - intros n IH word p Hword Hp.
   destruct(machine230_spare_successor_inv M n word Hword)as[old[Hold Eword]].
   destruct(power2_total M(N 3*n))as[q Hq].
   assert(Ep:p=N 8*q)by(eapply power2_functional;[exact Hp|now apply spare_power_step]).
   rewrite Eword,Ep.
   replace(N 7*(N 6+N 8*old)+N 6)with(N 8*(N 7*old+N 6))by(spare_constants;ring).
   rewrite(IH old q Hold Hq). ring.
Qed.
Theorem machine230_spare_append n word p:
 machine230_spare M n word->power2 M(N 3*n)p->
 machine230_spare M(S n)(word+N 6*p).
Proof.
 intros Hword Hp. pose proof(machine230_spare_power n word p Hword Hp)as E.
 replace(word+N 6*p)with(N 6+N 8*word).
 - now apply machine230_spare_successor.
 - rewrite <-E. spare_constants;ring.
Qed.
Theorem machine230_spare_append_iff n word p next:
 machine230_spare M n word->power2 M(N 3*n)p->
 (machine230_spare M(S n)next<->next=word+N 6*p).
Proof.
 intros Hw Hp;split.
 - intro Hnext. eapply machine230_spare_functional;[exact Hnext|].
   exact(machine230_spare_append n word p Hw Hp).
 - intro E. rewrite E. exact(machine230_spare_append n word p Hw Hp).
Qed.
End Power.
Print Assumptions machine230_spare_power.
Print Assumptions machine230_spare_append.
Print Assumptions machine230_spare_append_iff.
