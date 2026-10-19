(** * RM: the register machine implemented by Wade's TMBuilder framework.

    A program is a binary tree of cons cells with sharing (a DAG): node [n] has a car edge
    (taken when the IP bit read is 0) and a cdr edge (bit 1).  Leaves are register operations,
    [break k], [continue k] and [halt].

    Two semantics are given:
    - the path semantics ([rm_step]), which is what the Turing machine implements: the IP is a
      list of bits (MSB first, implicit trailing zeros) manipulated by increment / strip;
    - the structured big-step semantics ([run]), convenient for program proofs.
    Their equivalence is proved in RMEquiv.v. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.

Inductive edge : Type :=
  | ENode (n : nat)
  | EInc (r : nat)
  | EDecnz (r : nat)
  | EBreak (k : nat)
  | EContinue (k : nat)
  | EHalt.

Record prog : Type := mkProg {
  nodes : nat -> edge * edge;   (* car, cdr *)
  root  : nat;
  nnodes : nat;                 (* nodes >= nnodes are unused *)
}.

Definition regs := nat -> nat.
Definition upd (R : regs) (r v : nat) : regs := fun i => if Nat.eqb i r then v else R i.
Definition regs0 : regs := fun _ => 0.

(** ** Walking the tree with an IP.  [bit P i] is 0 beyond the end of [P]. *)
Definition bit (P : list bool) (i : nat) : bool := nth i P false.

(* [walk p fuel n P i] : follow edges from node [n] reading bits [P i], [P (i+1)], ... ;
   returns the leaf edge and the number of bits consumed in total (= depth of the leaf cell). *)
Fixpoint walk (p : prog) (fuel : nat) (n : nat) (P : list bool) (i : nat) : option (edge * nat) :=
  match fuel with
  | 0 => None
  | S fuel =>
    let '(a, b) := nodes p n in
    let e := if bit P i then b else a in
    match e with
    | ENode n' => walk p fuel n' P (S i)
    | _ => Some (e, S i)
    end
  end.

(** ** Path arithmetic.  Paths are MSB-first; arithmetic acts at the right end. *)

(* increment of the reversed list (LSB first) *)
Fixpoint inc_rev (l : list bool) : list bool :=
  match l with
  | [] => []                          (* overflow: the TM restarts with an all-zero IP *)
  | false :: l => true :: l
  | true :: l => false :: inc_rev l
  end.
Definition inc_path (P : list bool) : list bool := rev (inc_rev (rev P)).

(* strip bits from the right until [k] bits equal to [b] have been removed *)
Fixpoint strip_rev (b : bool) (k : nat) (l : list bool) : list bool :=
  match k with
  | 0 => l
  | S k =>
    match l with
    | [] => []
    | x :: l => if Bool.eqb x b then strip_rev b k l else strip_rev b (S k) l
    end
  end.
Definition strip_path (b : bool) (k : nat) (P : list bool) : list bool := rev (strip_rev b k (rev P)).

Definition brk (k : nat) (P : list bool) : list bool := inc_path (strip_path false k P).
Definition cont (k : nat) (P : list bool) : list bool := strip_path true k P.

(** ** Path small-step semantics. A configuration is (IP, registers). [None] = halt (or stuck). *)
Definition conf := (list bool * regs)%type.

Definition rm_step (p : prog) (c : conf) : option conf :=
  let '(P, R) := c in
  match walk p (nnodes p + 1) (root p) P 0 with
  | None => None
  | Some (e, d) =>
    let P := firstn d (P ++ repeat false d) in     (* the bits actually read *)
    match e with
    | ENode _ => None
    | EInc r => Some (inc_path P, upd R r (S (R r)))
    | EDecnz r => match R r with
                  | 0 => Some (brk 1 P, R)
                  | S v => Some (inc_path P, upd R r v)
                  end
    | EBreak k => Some (brk k P, R)
    | EContinue k => Some (cont k P, R)
    | EHalt => None
    end
  end.

Fixpoint rm_run (p : prog) (fuel : nat) (c : conf) : option conf :=
  match fuel with
  | 0 => Some c
  | S fuel => match rm_step p c with None => None | Some c' => rm_run p fuel c' end
  end.

(* the TM halts iff the program reaches the halt leaf *)
Definition at_halt (p : prog) (c : conf) : Prop :=
  exists d, walk p (nnodes p + 1) (root p) (fst c) 0 = Some (EHalt, d).

Definition rm_halts (p : prog) (c : conf) : Prop :=
  exists n c', rm_run p n c = Some c' /\ at_halt p c'.

(** ** Structured big-step semantics. *)
Inductive exit : Type := XNormal | XBreak (k : nat) | XContinue (k : nat) | XHalt.

(* [run p e R x R'] : executing edge [e] from registers [R] terminates with exit [x] and registers [R'].
   Invariant: XBreak k and XContinue k carry k >= 1. *)
Inductive run (p : prog) : edge -> regs -> exit -> regs -> Prop :=
  | run_inc r R :
      run p (EInc r) R XNormal (upd R r (S (R r)))
  | run_decnz_pos r R v :
      R r = S v -> run p (EDecnz r) R XNormal (upd R r v)
  | run_decnz_zero r R :
      R r = 0 -> run p (EDecnz r) R (XBreak 1) R
  | run_break0 R :
      run p (EBreak 0) R XNormal R
  | run_breakS k R :
      run p (EBreak (S k)) R (XBreak (S k)) R
  | run_continue k R :
      run p (EContinue (S k)) R (XContinue (S k)) R
  | run_halt R :
      run p EHalt R XHalt R
  (* cons cell: car first *)
  | run_node_car_break1 n R R' :
      run p (fst (nodes p n)) R (XBreak 1) R' ->
      run p (ENode n) R XNormal R'
  | run_node_car_breakS n k R R' :
      run p (fst (nodes p n)) R (XBreak (S (S k))) R' ->
      run p (ENode n) R (XBreak (S k)) R'
  | run_node_car_continue n k R R' :
      run p (fst (nodes p n)) R (XContinue (S k)) R' ->
      run p (ENode n) R (XContinue (S k)) R'
  | run_node_car_halt n R R' :
      run p (fst (nodes p n)) R XHalt R' ->
      run p (ENode n) R XHalt R'
  (* car finished normally: run the cdr *)
  | run_node_cdr_normal n R R1 R' :
      run p (fst (nodes p n)) R XNormal R1 ->
      run p (snd (nodes p n)) R1 XNormal R' ->
      run p (ENode n) R XNormal R'
  | run_node_cdr_break n k R R1 R' :
      run p (fst (nodes p n)) R XNormal R1 ->
      run p (snd (nodes p n)) R1 (XBreak (S k)) R' ->
      run p (ENode n) R (XBreak (S k)) R'
  | run_node_cdr_continue1 n R R1 R2 x R' :
      run p (fst (nodes p n)) R XNormal R1 ->
      run p (snd (nodes p n)) R1 (XContinue 1) R2 ->
      run p (ENode n) R2 x R' ->              (* loop: restart this cons *)
      run p (ENode n) R x R'
  | run_node_cdr_continueS n k R R1 R' :
      run p (fst (nodes p n)) R XNormal R1 ->
      run p (snd (nodes p n)) R1 (XContinue (S (S k))) R' ->
      run p (ENode n) R (XContinue (S k)) R'
  | run_node_cdr_halt n R R1 R' :
      run p (fst (nodes p n)) R XNormal R1 ->
      run p (snd (nodes p n)) R1 XHalt R' ->
      run p (ENode n) R XHalt R'.

(* iterate main(): the IP overflows at the end of main() and restarts from the root *)
Inductive iter_halts (p : prog) : regs -> Prop :=
  | iter_halt R R' : run p (ENode (root p)) R XHalt R' -> iter_halts p R
  | iter_next R R' : run p (ENode (root p)) R XNormal R' -> iter_halts p R' -> iter_halts p R.

(* Well-formedness needed for the equivalence: no break/continue escapes the root. *)
Definition wf_run (p : prog) : Prop :=
  forall R x R', run p (ENode (root p)) R x R' -> x = XNormal \/ x = XHalt.
