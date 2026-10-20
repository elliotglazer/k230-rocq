(** Definable finite register files in the exact physical runtime order.
    The spare tail is an arbitrary internal binary word. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 PowerTwoSyntax TM230UnaryBlocks.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition machine230_unary_block_formula(value tail word:term):form:=
 ∃∃(power2_formula(σ(code_lift2 value))$1 ∧
  ($1==σ $0 ∧code_lift2 word==
    (num 2⊗$0)⊕((num 2⊗$1)⊗code_lift2 tail))).
Definition machine230_marked_block_formula(value tail word:term):form:=
 ∃∃(power2_formula(code_lift2 value)$1 ∧
  ($1==σ $0 ∧code_lift2 word==
    (num 4⊗$0)⊕((num 4⊗$1)⊗code_lift2 tail))).
Lemma register_eval_succ M rho t:evalM M rho(σ t)=succM M(evalM M rho t).
Proof. reflexivity. Qed.
Lemma register_eval_add M rho t u:evalM M rho(t⊕u)=addM M(evalM M rho t)(evalM M rho u).
Proof. reflexivity. Qed.
Lemma register_eval_mul M rho t u:evalM M rho(t⊗u)=mulM M(evalM M rho t)(evalM M rho u).
Proof. reflexivity. Qed.
Lemma register_eval_up M rho x t:evalM M(x.:rho)t`[↑]=evalM M rho t.
Proof. unfold evalM. now rewrite eval_up. Qed.
Local Opaque holds power2_formula.
Theorem machine230_unary_block_formula_correct M rho value tail word:
 holds M rho(machine230_unary_block_formula value tail word)<->
 machine230_unary_block M(evalM M rho value)(evalM M rho tail)(evalM M rho word).
Proof.
 unfold machine230_unary_block_formula,machine230_unary_block.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite power2_formula_correct. setoid_rewrite power_holds_equal.
 repeat setoid_rewrite register_eval_succ. repeat setoid_rewrite register_eval_add.
 repeat setoid_rewrite register_eval_mul. repeat setoid_rewrite code_eval_num.
 repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.
Theorem machine230_marked_block_formula_correct M rho value tail word:
 holds M rho(machine230_marked_block_formula value tail word)<->
 machine230_marked_block M(evalM M rho value)(evalM M rho tail)(evalM M rho word).
Proof.
 unfold machine230_marked_block_formula,machine230_marked_block.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite power2_formula_correct. setoid_rewrite power_holds_equal.
 repeat setoid_rewrite register_eval_succ. repeat setoid_rewrite register_eval_add.
 repeat setoid_rewrite register_eval_mul. repeat setoid_rewrite code_eval_num.
 repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Fixpoint machine230_blocks_at M(n:nat)(values:nat->carrier M)tail word:Prop:=
 match n with
 |0=>word=tail
 |S n=>exists middle,machine230_blocks_at M n(fun idx =>values(S idx))tail middle /\
   machine230_unary_block M(values 0)middle word
 end.
Fixpoint machine230_blocks_formula(n:nat)(values:nat->term)(tail word:term):form:=
 match n with
 |0=>word==tail
 |S n=>∃(machine230_blocks_formula n(fun idx =>(values(S idx))`[↑])tail`[↑] $0 ∧
   machine230_unary_block_formula(values 0)`[↑] $0 word`[↑])
 end.

Theorem machine230_blocks_total M n values tail:
 exists word,machine230_blocks_at M n values tail word.
Proof.
 induction n in values|-*;cbn[machine230_blocks_at].
 - exists tail;reflexivity.
 - destruct(IHn(fun idx =>values(S idx)))as[middle Hm].
   destruct(machine230_unary_block_total M(values 0)middle)as[word Hw].
   exists word,middle;auto.
Qed.
Theorem machine230_blocks_functional M n values tail x y:
 machine230_blocks_at M n values tail x ->machine230_blocks_at M n values tail y ->x=y.
Proof.
 induction n in values,x,y|-*;cbn[machine230_blocks_at].
 - congruence.
 - intros[middle[Hm Hx]][other[Ho Hy]].
   assert(E:middle=other)by(eapply IHn;eassumption). subst other.
   eapply machine230_unary_block_functional;eassumption.
Qed.
Theorem machine230_blocks_ext M n values other tail word:
 (forall idx,values idx=other idx)->
 (machine230_blocks_at M n values tail word<->machine230_blocks_at M n other tail word).
Proof.
 induction n in values,other,tail,word|-*;intro H;cbn[machine230_blocks_at];[reflexivity|].
 assert(E:values 0=other 0)by apply H. rewrite E.
 assert(IH:forall middle,machine230_blocks_at M n(fun idx =>values(S idx))tail middle<->
   machine230_blocks_at M n(fun idx =>other(S idx))tail middle).
 {intro middle;apply IHn;intro idx;apply H. }
 now setoid_rewrite IH.
Qed.
Theorem machine230_blocks_formula_correct M n values tail word rho:
 holds M rho(machine230_blocks_formula n values tail word)<->
 machine230_blocks_at M n(fun idx =>evalM M rho(values idx))(evalM M rho tail)(evalM M rho word).
Proof.
 induction n in values,tail,word,rho|-*;cbn[machine230_blocks_formula machine230_blocks_at].
 - apply power_holds_equal.
 - rewrite holds_ex. setoid_rewrite holds_and.
   setoid_rewrite IHn. setoid_rewrite machine230_unary_block_formula_correct.
   assert(Hrest:forall middle,
     machine230_blocks_at M n
       (fun idx =>evalM M(middle.:rho)(values(S idx))`[↑])
       (evalM M(middle.:rho)tail`[↑])(evalM M(middle.:rho)$0)<->
     machine230_blocks_at M n(fun idx =>evalM M rho(values(S idx)))
       (evalM M rho tail)middle).
   {intro middle. rewrite(register_eval_up M rho middle tail).
    apply machine230_blocks_ext. intro idx. apply register_eval_up. }
   assert(Hhead:forall middle,
     machine230_unary_block M(evalM M(middle.:rho)(values 0)`[↑])
       (evalM M(middle.:rho)$0)(evalM M(middle.:rho)word`[↑])<->
     machine230_unary_block M(evalM M rho(values 0))middle(evalM M rho word)).
   {intro middle. rewrite !register_eval_up. reflexivity. }
   split;intros[middle[Hm Hw]];exists middle;split.
   + exact(proj1(Hrest middle)Hm).
   + exact(proj1(Hhead middle)Hw).
   + exact(proj2(Hrest middle)Hm).
   + exact(proj2(Hhead middle)Hw).
Qed.

(** Interpreter230Check.v's pinned permutation, as a finite meta-level map.
    Logical registers 0..8 appear physically as 2,8,1,4,3,7,0,5,6. *)
Definition machine230_physical_order:list nat:=[2;8;1;4;3;7;0;5;6].
Definition machine230_physical_register(idx:nat):nat:=nth idx machine230_physical_order 0.
Definition machine230_register_file M(registers:nat->carrier M)spare word:Prop:=
 machine230_blocks_at M 9(fun idx =>registers(machine230_physical_register idx))spare word.
Definition machine230_register_file_formula(registers:nat->term)(spare word:term):form:=
 machine230_blocks_formula 9(fun idx =>registers(machine230_physical_register idx))spare word.
Theorem machine230_register_file_total M registers spare:
 exists word,machine230_register_file M registers spare word.
Proof. apply machine230_blocks_total. Qed.
Theorem machine230_register_file_functional M registers spare x y:
 machine230_register_file M registers spare x ->machine230_register_file M registers spare y ->x=y.
Proof. apply machine230_blocks_functional. Qed.
Theorem machine230_register_file_formula_correct M rho registers spare word:
 holds M rho(machine230_register_file_formula registers spare word)<->
 machine230_register_file M(fun idx =>evalM M rho(registers idx))(evalM M rho spare)(evalM M rho word).
Proof. apply machine230_blocks_formula_correct. Qed.
Theorem machine230_register_file_physical_order M registers spare word:
 machine230_register_file M registers spare word <->
 exists w1 w2 w3 w4 w5 w6 w7 w8,
 machine230_unary_block M(registers 2)w1 word /\
 machine230_unary_block M(registers 8)w2 w1 /\
 machine230_unary_block M(registers 1)w3 w2 /\
 machine230_unary_block M(registers 4)w4 w3 /\
 machine230_unary_block M(registers 3)w5 w4 /\
 machine230_unary_block M(registers 7)w6 w5 /\
 machine230_unary_block M(registers 0)w7 w6 /\
 machine230_unary_block M(registers 5)w8 w7 /\
 machine230_unary_block M(registers 6)spare w8.
Proof.
 unfold machine230_register_file,machine230_physical_register,machine230_physical_order.
 cbn[machine230_blocks_at nth].
 split.
 - intro H. destruct H as[a[H H0]]. destruct H as[b[H H1]].
   destruct H as[c[H H2]]. destruct H as[d[H H3]].
   destruct H as[e[H H4]]. destruct H as[f[H H5]].
   destruct H as[g[H H6]]. destruct H as[h[H H7]].
   destruct H as[last[E H8]]. subst last.
   exists a,b,c,d,e,f,g,h. tauto.
 - intros(a&b&c&d&e&f&g&h&H0&H1&H2&H3&H4&H5&H6&H7&H8).
   exists a. split;[|exact H0]. exists b. split;[|exact H1].
   exists c. split;[|exact H2]. exists d. split;[|exact H3].
   exists e. split;[|exact H4]. exists f. split;[|exact H5].
   exists g. split;[|exact H6]. exists h. split;[|exact H7].
   exists spare;auto.
Qed.
Print Assumptions machine230_unary_block_formula_correct.
Print Assumptions machine230_register_file_total.
Print Assumptions machine230_register_file_formula_correct.
Print Assumptions machine230_register_file_physical_order.
