(** Concrete physical register files for the exact finite runtime oracle.
    The first nine values are model elements; spare multiplicity is internal. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 TM230UnaryBlocks TM230RegisterPrefix TM230SpareSyntax TM230SpareRecurrence TM230SparePower TM230SpareBlocks.
From K230 Require Runtime230Core.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Module Runtime230:=K230.Runtime230Core.
Fixpoint machine230_marked_blocks_list M r(values:list(carrier M))tail word:Prop:=
 match values with
 |[]=>False
 |v::vs=>match r with
   |0=>exists middle,machine230_blocks_list M vs tail middle /\machine230_marked_block M v middle word
   |S r=>exists middle,machine230_marked_blocks_list M r vs tail middle /\machine230_unary_block M v middle word
   end
 end.
Definition machine230_update_values {D}(r:nat)(value:D)(values:list D):list D:=
 firstn r values++value::skipn(S r)values.
Definition machine230_effect_values M eff(values updated:list(carrier M)):Prop:=
 match eff with
 |Runtime230.FNone=>updated=values
 |Runtime230.FInc r=>exists old,nth_error values r=Some old /\
   updated=machine230_update_values r(succM M old)values
 |Runtime230.FDec r=>exists old new,nth_error values r=Some old /\
   ((old=zeroM M /\new=zeroM M) \/old=succM M new) /\
   updated=machine230_update_values r new values
 end.
Definition machine230_runtime_box M(values:list(carrier M))E(x:Runtime230.boxst)word:Prop:=
 length values=9%nat /\coding_lt M(zeroM M)E /\
 match x with
 |Runtime230.BPlain eff=>exists updated spare,machine230_effect_values M eff values updated /\
   machine230_spare M(match eff with Runtime230.FInc _=>succM M E|_=>E end)spare /\
   machine230_blocks_list M updated spare word
 |Runtime230.BMark r=>exists spare,machine230_spare M E spare /\
   machine230_marked_blocks_list M r values spare word
 end.
Definition machine230_runtime_branch_valid M(values:list(carrier M))(br:Runtime230.branch):Prop:=
 match br with
 |None=>True
 |Some(r,z)=>if z then nth r values(zeroM M)=zeroM M else nth r values(zeroM M)<>zeroM M
 end.
Section Lists.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring runtime_box_ring:(model_semiring M).
Lemma machine230_blocks_list_append prefix suffix tail word:
 machine230_blocks_list M(prefix++suffix)tail word <->
 exists middle,machine230_blocks_list M suffix tail middle /\machine230_blocks_list M prefix middle word.
Proof.
 induction prefix as[|v prefix IH]in word|-*;cbn[machine230_blocks_list].
 -split;intro H;[exists word;auto|destruct H as[middle[H ->]];exact H].
 -split.
  +intros[inside[Hinside Hhead]]. apply IH in Hinside.
   destruct Hinside as[middle[Hsuffix Hprefix]]. exists middle. split;[exact Hsuffix|]. exists inside;auto.
  +intros[middle[Hsuffix[inside[Hprefix Hhead]]]]. exists inside. split;[|exact Hhead].
   apply IH;exists middle;auto.
Qed.
Lemma machine230_nth_decomposition {D}(values:list D)r v:
 nth_error values r=Some v->values=firstn r values++v::skipn(S r)values.
Proof.
 induction values as[|x values IH]in r|-*;destruct r;cbn;intro H;try discriminate.
 -injection H as <-;reflexivity.
 -f_equal;now apply IH.
Qed.
Lemma machine230_update_length {D}(values:list D)r old new:
 nth_error values r=Some old->length(machine230_update_values r new values)=length values.
Proof.
 intro H. pose proof(machine230_nth_decomposition values r old H)as E.
 pose proof(f_equal (@length D)E)as EL. rewrite length_app in EL. cbn[length]in EL. unfold machine230_update_values. rewrite length_app. cbn[length]. symmetry;exact EL.
Qed.
Lemma machine230_effect_length eff values updated:
 machine230_effect_values M eff values updated->length updated=length values.
Proof.
 destruct eff as[|r|r];cbn[machine230_effect_values].
 -now intros ->.
 -intros[old[H ->]]. now apply(machine230_update_length values r old).
 -intros[old[new[H[_ ->]]]]. now apply(machine230_update_length values r old).
Qed.
Lemma machine230_blocks_list_split values r v tail word:
 nth_error values r=Some v->machine230_blocks_list M values tail word->
 exists inside target,machine230_blocks_list M(skipn(S r)values)tail inside /\
 machine230_unary_block M v inside target /\machine230_blocks_list M(firstn r values)target word.
Proof.
 intros HN HB. rewrite(machine230_nth_decomposition values r v HN)in HB.
 apply machine230_blocks_list_append in HB. destruct HB as[target[HT HP]].
 cbn[machine230_blocks_list]in HT. destruct HT as[inside[HI HV]]. exists inside,target;auto.
Qed.
Lemma machine230_blocks_list_join values r v tail inside target word:
 nth_error values r=Some v->machine230_blocks_list M(skipn(S r)values)tail inside->
 machine230_unary_block M v inside target->machine230_blocks_list M(firstn r values)target word->
 machine230_blocks_list M values tail word.
Proof.
 intros HN HI HV HP. rewrite(machine230_nth_decomposition values r v HN).
 apply machine230_blocks_list_append. exists target. split;[exists inside;auto|exact HP].
Qed.
Lemma machine230_blocks_list_update values r old new tail inside target word:
 nth_error values r=Some old->machine230_blocks_list M(skipn(S r)values)tail inside->
 machine230_unary_block M new inside target->machine230_blocks_list M(firstn r values)target word->
 machine230_blocks_list M(machine230_update_values r new values)tail word.
Proof.
 intros HN HI HV HP. unfold machine230_update_values.
 apply machine230_blocks_list_append. exists target. split;[exists inside;auto|exact HP].
Qed.
Lemma machine230_marked_blocks_split values r v tail word:
 nth_error values r=Some v->machine230_marked_blocks_list M r values tail word->
 exists inside target,machine230_blocks_list M(skipn(S r)values)tail inside /\
 machine230_marked_block M v inside target /\machine230_blocks_list M(firstn r values)target word.
Proof.
 induction values as[|x values IH]in r,word|-*;destruct r;cbn;intros HN HB;try discriminate.
 -injection HN as <-. destruct HB as[inside[HI HV]]. exists inside,word;auto.
 -destruct HB as[middle[HM HV]]. destruct(IH r middle HN HM)as[inside[target[HI[HT HP]]]].
  exists inside,target. split;[exact HI|]. split;[exact HT|]. exists middle;auto.
Qed.
Lemma machine230_marked_blocks_join values r v tail inside target word:
 nth_error values r=Some v->machine230_blocks_list M(skipn(S r)values)tail inside->
 machine230_marked_block M v inside target->machine230_blocks_list M(firstn r values)target word->
 machine230_marked_blocks_list M r values tail word.
Proof.
 induction values as[|x values IH]in r,word|-*;destruct r;cbn;intros HN HI HV HP;try discriminate.
 -injection HN as <-. subst word. exists inside;auto.
 -destruct HP as[middle[HT HX]]. exists middle. split;[|exact HX].
  exact(IH r middle HN HI HV HT).
Qed.
Lemma machine230_unary_block_even value tail word:
 machine230_unary_block M value tail word->exists rest,word=N 2*rest.
Proof.
 intros[p[k[HP[Hpk E]]]]. exists(addM M k(mulM M p tail)). rewrite E;ring.
Qed.
Lemma machine230_marked_block_even value tail word:
 machine230_marked_block M value tail word->exists rest,word=N 2*rest.
Proof.
 intros[p[k[HP[Hpk E]]]]. exists(mulM M(N 2)(addM M k(mulM M p tail))).
 rewrite E. cbn[code_numeral]. repeat multimatch goal with | |- context[succM M ?x]=>lazymatch x with | zeroM _=>fail 0 | _=>rewrite(succ_as_add M x) end end. ring.
Qed.
End Lists.
Print Assumptions machine230_effect_length.
Print Assumptions machine230_marked_blocks_split.
Print Assumptions machine230_marked_blocks_join.
Print Assumptions machine230_marked_block_even.