(** Arithmetic dispatcher invariant. The PC includes its leading sentinel;
    [low] is the tape prefix without that sentinel. All four parameters,
    including the blank gap, may be nonstandard elements of the PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive TM230BinaryStep TM230BitArithmetic.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Definition machine230_dispatch_code_view M pc depth gap file s :=exists low p q,
 power2 M depth p /\coding_lt M low p /\pc=addM M low p /\power2 M gap q /\
 machine230_right_view M 84(succM M(zeroM M))
 (addM M low(mulM M(mulM M p q)(addM M(succM M(zeroM M))
 (mulM M(succM M(succM M(zeroM M)))file))))s.
Definition machine230_dispatch_code_formula(pc depth gap file state left head right:term):form:=
 ∃∃∃(power2_formula(power_lift3 depth)$1 ∧
 (Peano.sless $2 $1 ∧(power_lift3 pc==$2⊕$1 ∧
 (power2_formula(power_lift3 gap)$0 ∧
 (power_lift3 state==num 84 ∧(power_lift3 left==num 1 ∧
 ((power_lift3 head==zero ∨power_lift3 head==num 1) ∧
 $2⊕(($1⊗$0)⊗(num 1⊕(num 2⊗power_lift3 file)))==
 (num 2⊗power_lift3 right)⊕power_lift3 head))))))).
Local Opaque holds power2_formula Peano.sless.
Theorem machine230_dispatch_code_formula_correct M rho pc depth gap file state left head right:
 holds M rho(machine230_dispatch_code_formula pc depth gap file state left head right)<->
 machine230_dispatch_code_view M(evalM M rho pc)(evalM M rho depth)(evalM M rho gap)
 (evalM M rho file)(machine230_mk_config(carrier M)(evalM M rho state)(evalM M rho left)
 (evalM M rho head)(evalM M rho right)).
Proof.
 unfold machine230_dispatch_code_formula,machine230_dispatch_code_view,machine230_right_view,machine230_is_bit.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite holds_or. setoid_rewrite power2_formula_correct.
 setoid_rewrite less_formula_correct. setoid_rewrite machine230_holds_equal.
 repeat first[progress(setoid_rewrite machine230_eval_add)|progress(setoid_rewrite machine230_eval_mul)].
 repeat setoid_rewrite power_lift3_eval. repeat setoid_rewrite code_eval_num.
 reflexivity.
Qed.
Theorem machine230_dispatch_code_unique M pc depth gap file s t:
 machine230_dispatch_code_view M pc depth gap file s ->
 machine230_dispatch_code_view M pc depth gap file t ->s=t.
Proof.
 intros[l[p[q[Hp[Hlp[Ec[Hq Hs]]]]]]][l'[p'[q'[Hp'[Hlp'[Ec'[Hq' Ht]]]]]]].
 pose proof(power2_functional M depth p p' Hp Hp')as Ep;subst p'.
 pose proof(power2_functional M gap q q' Hq Hq')as Eq;subst q'.
 assert(El:l=l')by(apply(Arithmetic.add_cancel M l l' p);now rewrite <-Ec,<-Ec').
 subst l';eapply machine230_right_view_unique;[exact Hs|exact Ht].
Qed.
Theorem machine230_dispatch_code_positive M pc depth gap file s:
 machine230_dispatch_code_view M pc depth gap file s ->coding_lt M(zeroM M)pc.
Proof.
 intros[l[p[q[Hp[Hlp[-> [Hq Hs]]]]]]].
 destruct(power2_positive_successor M depth p Hp)as[k ->].
 rewrite(Arithmetic.add_comm M l(succM M k)),(Arithmetic.add_succ M k l). apply coding_zero_lt_succ.
Qed.
Print Assumptions machine230_dispatch_code_formula_correct.
Print Assumptions machine230_dispatch_code_unique.
Print Assumptions machine230_dispatch_code_positive.
