(* http://coq.inria.fr/cocorico/AUGER_ExtractionTuto : *)
Require ExtrOcamlBasic.
Require ExtrOcamlBigIntConv.
Require ExtrOcamlIntConv.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlNatInt.
Require ExtrOcamlString.
Require ExtrOcamlZBigInt.
Require ExtrOcamlZInt.

Module OcamlChar.

Parameter t : Set.
Extract Constant t => "char".

Definition char : Set := t.


Parameter char_eq : char -> char -> bool.
Extract Inlined Constant char_eq => " ( == ) ".

Parameter char_le : char -> char -> bool.
Extract Inlined Constant char_le => " ( <= ) ".

End OcamlChar.

Module OcamlInt.

(*Parameter t : Set.
Extract Constant t => "int".
*)

Definition int : Type := ExtrOcamlIntConv.int.

Definition int_of_nat := ExtrOcamlIntConv.int_of_nat.

Definition nat_of_int_pos := ExtrOcamlIntConv.nat_of_int.

Parameter int_eq : int -> int -> bool.
Extract Inlined Constant int_eq => "( == )".

Axiom int_eq_to_prop :
  forall a b : int,
  int_eq a b = true -> a = b
.
Axiom int_neq_to_prop :
  forall a b : int,
  (int_eq a b = false) = ((a = b) -> False)
.
Hint Rewrite int_eq_to_prop int_neq_to_prop
  : eq_to_prop
.


Parameter int_le : int -> int -> bool.
Extract Inlined Constant int_le => "( <= )".

Parameter int_sub : int -> int -> int.
Extract Inlined Constant int_sub => "( - )".

Definition int_zero := ExtrOcamlIntConv.int_zero.


  Module NoOverflow.
    (* axioms that assume non-overflowing int *)

    Axiom minus_nat_of_int :
      forall (a b : int),
      int_le int_zero a = true ->
      int_le int_zero b = true ->
      int_le b a = true  (* a >= b*) ->
      nat_of_int_pos (int_sub a b) =
      (nat_of_int_pos a) - (nat_of_int_pos b)
    .

    Axiom minus_rev_le :
      forall (a b c : int),
      int_le a b = int_le (int_sub c b) (int_sub c a)
    .

    Axiom int_sub_le_zero :
      forall a b : int,
      (int_le a b) = true ->
      (int_le int_zero (int_sub b a)) = true
    .

  End NoOverflow.


  Axiom nat_le_of_int :
    forall a b : int,
    (int_le int_zero a) = true ->
    (int_le int_zero b) = true ->
    (int_le a b) = true ->
    nat_of_int_pos a <= nat_of_int_pos b
  .

  Axiom eq_of_nat_eq :
    forall a b : int,
    (int_le int_zero a) = true ->
    (int_le int_zero b) = true ->
    nat_of_int_pos a = nat_of_int_pos b ->
    a = b
  .

  Axiom eq_of_sub_eq :
    forall a b c : int,
    (int_sub a b) = (int_sub a c) ->
    b = c
  .

End OcamlInt.

Class TcArith (A : Type) :=
  { sub : A -> A -> A
  }
.
Extraction Inline sub.

Instance OcamlInt_Arith : TcArith OcamlInt.int :=
  { sub := OcamlInt.int_sub
  }
.
Extraction Inline OcamlInt_Arith.

Instance nat_Arith : TcArith nat :=
  { sub := minus%nat
  }
.
Extraction Inline nat_Arith.

Definition class_sub :=
  fun {A : Type} {ar : TcArith A} (x y : A) =>
    sub x y
.
Extraction Inline class_sub.

Notation "a - b" := (class_sub a b).


(*****************)

Module OcamlCmp.

(* todo: to move into separate module. *)

(* purpose: use "==" for ocaml structural equality
   for ints, chars and other basic ocaml types. *)

Class Cmp (A : Type) :=
  { eq : A -> A -> bool
  ; le : A -> A -> bool
  }
.
Extraction Inline eq.
Extraction Inline le.
Hint Unfold eq : eq_to_prop.


Instance char_Cmp : Cmp OcamlChar.char :=
  { eq := OcamlChar.char_eq
  ; le := OcamlChar.char_le
  }
.

Extraction Inline char_Cmp.


Instance int_Cmp : Cmp OcamlInt.int :=
  { eq := OcamlInt.int_eq
  ; le := OcamlInt.int_le
  }
.

Extraction Inline int_Cmp.

Definition class_eq :=
  fun {A : Type} {cmpa : Cmp A} (x y : A) =>
    eq x y
.

Extraction Inline class_eq.

Definition class_le :=
  fun {A : Type} {cmpa : Cmp A} (x y : A) =>
    le x y
.

Extraction Inline class_le.


Axiom class_le_x_x :
  forall A, forall (x : A), forall (cmpa : Cmp A),
  class_le x x = true.

End OcamlCmp.

Notation "x == y" := (OcamlCmp.class_eq x y) (at level 70, no associativity).

Notation "x = y" := (x == y) : oc_scope.

Notation "x <== y" := (OcamlCmp.class_le x y) (at level 70, no associativity).

Notation "x <= y" := (x <== y) : oc_scope.

Delimit Scope oc_scope with oc.

(* Eval compute in ((OcamlInt.int_of_nat 3) = (OcamlInt.int_of_nat 2))%oc. *)
(* Eval compute in ((OcamlInt.int_of_nat 3) <== (OcamlInt.int_of_nat 2)). *)


(*****************)


Module Kmb_coq.

Require Import Coq.Lists.List.
Require Import ExtrOcamlIntConv.

Import OcamlChar.
Import OcamlInt.  Import OcamlInt.NoOverflow.
Import OcamlCmp.


Parameter input : Type.
Extract Constant input => "Kmb_input.input".

Parameter end_of_file : input -> bool.
Extract Constant end_of_file => "Kmb_input.end_of_file".

Parameter incr_pos : input -> input.
Extract Constant incr_pos => "Kmb_input.incr_pos".

Parameter get_current : input -> char.
Extract Constant get_current => "Kmb_input.get_current".

Parameter input_pos : input -> int.
Extract Inlined Constant input_pos => "(fun i -> i.pos)".

Parameter input_len : input -> int.
Extract Inlined Constant input_len => "(fun i -> i.len)".


Inductive result (A : Type) :=
  | Parsed : A -> input -> result A
  | Failed
.
Implicit Arguments Parsed [A].
Implicit Arguments Failed [A].


Section input_axioms.

Variable inp : input.

Axiom input_high_bound :
  (input_pos inp <== input_len inp) = true
.

Axiom input_pos_low_bound :
  (int_zero <== input_pos inp) = true
.

Axiom input_len_low_bound :
  (int_zero <== input_len inp) = true
.

Axiom input_len_const :
  forall (A : Type),
  forall (pa : input -> result A),
  forall (inp : input),
  match pa inp with
  | Failed => True
  | Parsed _ inp' => input_len inp = input_len inp'
  end
.


Definition input_left : int
 :=
   (input_len inp) - (input_pos inp)
.

Theorem input_left_low_bound :
  (int_zero <== input_left) = true
.
unfold input_left.
apply int_sub_le_zero.
exact input_high_bound.
Defined.

Definition input_left_nat : nat
 :=
   nat_of_int_pos input_left
.

Definition input_left_pos :
  int_le int_zero (input_len inp - input_pos inp) = true.
apply int_sub_le_zero.
apply input_high_bound.
Defined.

End input_axioms.

Hint Resolve
  input_high_bound
  input_pos_low_bound
  input_len_low_bound
  input_left_low_bound
  input_left_pos
  : inp.


Lemma input_left_of_pos :
  forall i1 i2 : input,
  input_len i1 = input_len i2 ->
  input_pos i1 = input_pos i2 ->
  input_left_nat i1 = input_left_nat i2
.
intros i1 i2 Hlen Hpos.
unfold input_left_nat.
unfold input_left.
rewrite Hlen.
rewrite Hpos.
reflexivity.
Defined.

Lemma input_pos_of_left :
  forall i1 i2 : input,
  input_len i1 = input_len i2 ->
  input_left_nat i1 = input_left_nat i2 ->
  input_pos i1 = input_pos i2
.
intros i1 i2 Hlen Hleft.
unfold input_left_nat in Hleft.
unfold input_left in Hleft.
apply eq_of_nat_eq in Hleft.
rewrite Hlen in Hleft.
unfold eq in Hleft.
apply eq_of_sub_eq in Hleft.
exact Hleft.
auto with inp.
auto with inp.
Defined.



Definition nondecr
  {A : Type}
  (cond : input -> result A)
  :
  Prop
  :=
  forall i_before,
  match cond i_before with
    | Parsed _ i_after =>
        (input_pos i_before <== input_pos i_after) = true
    | Failed => True
  end
.


Inductive par (A : Type) (pa : input -> result A) : Prop :=
  | Par : nondecr pa -> par A pa.

Ltac t_par :=
  repeat
    ( ( match goal with
        | [ |- par _ _ ]
            => constructor

        | [ |- nondecr _ ]
            => unfold nondecr; intros

        | [ H : par _ ?cond |- _ ] =>
            let Hnc := fresh "nondecr_" cond in
            case H; intro nondecr_cond

        | _ => apply class_le_x_x; auto

        end
      )
    )
.


Definition ret := fun {A} (a : A) input => Parsed a input.

Definition par_ret : forall A, forall (a : A), par A (ret a).
intros; unfold ret; t_par.
Qed.


Definition transform :=
  fun {A B} (r : input -> result A) (f : A -> B) input =>
    match r input with
      | Parsed v input' => Parsed (f v) input'
      | Failed => Failed
    end
.

Definition predicate_not :=
  fun {A} (cond : input -> result A) (inp : input) =>
    match cond inp with
      | Parsed _ _ => Failed
      | Failed => Parsed tt inp
    end
.

Definition predicate_and :=
  fun {A} (cond : input -> result A) (inp : input) =>
    match cond inp with
      | Parsed r _ => Parsed r inp
      | Failed as failed => failed
    end
.

Definition predicate_and' :=
  fun {A} (cond : input -> result A) inp =>
    predicate_not (fun inp' => predicate_not cond inp') inp
.


Ltac t_pass_par__ :=
(*  repeat *)
    (match goal with
     | [ H : par _ ?cond |- context Q
              [match (?cond ?input) with
               | Parsed _ _ => _
               | Failed => _
               end
              ]
       ] =>
           apply H in Q
     end
    )
.


Ltac t_lens :=
  try (
  match goal with
    | [ H : (input_len ?a = input_len ?b) |- _ ] =>
          rewrite H
  end
  )
.


Ltac t_unit :=
  repeat
    (match goal with [ H : unit |- _ ] => destruct H end)
.


Ltac t_result :=
  let any_match cond input :=
           let Hconst := fresh "input_len_const_" input in
           (
           pose proof (input_len_const _ cond input)
              as Hconst;

           destruct (cond input)
           )
  in
  t_par;
  repeat
    (match goal with
     | [ N : nondecr ?cond |- context
              [match (?cond ?input) with
               | Parsed _ _ => _
               | Failed => _
               end
              ]
       ] =>
           let Hnd := fresh "nondecr_input_" cond in
           assert (Hnd := N input);
           any_match cond input
     |
       [ |- context
              [match (?cond ?input) with
               | Parsed _ _ => _
               | Failed => _
               end
              ]
       ] =>
           any_match cond input

     end
    );
  t_lens;
  t_unit;
  auto
.


Theorem and_eq_and'
 : forall (cond : _ -> result unit) inp,
   predicate_and cond inp = predicate_and' cond inp
.
intros; compute; t_result; t_unit; auto.
Qed.



Definition peg_stub := fun inp => Parsed tt inp.

Definition opt :=
  fun {A} (cond : input -> result A) input =>
    match cond input with
      | Parsed _ input' => Parsed tt input'
      | Failed => Parsed tt input
    end
.

Definition opt_accu :=
  fun {A} (cond : input -> result A) input =>
    match cond input with
      | Parsed r input' => Parsed (Some r) input'
      | Failed => Parsed None input
    end
.

Definition test_any :=
  fun input =>
    if end_of_file input then
      Failed
    else
      (* let _curr = get_current input in *)
      Parsed tt (incr_pos input)
.


Definition test_char :=
  fun c input =>
    if end_of_file input
    then
      Failed
    else
      let curr := get_current input in
      if curr == c
      then
        Parsed tt (incr_pos input)
      else
        Failed
.



Fixpoint match_pattern cs input :=
  match cs with
  | nil => Parsed tt input
  | x :: xs =>
      if end_of_file input
      then
        Failed
      else
        let curr := get_current input in
        if curr == x then
          match_pattern xs (incr_pos input)
        else
          Failed
  end
.


Definition test_class :=
  fun (fn : _ -> bool) input =>
    if end_of_file input
    then
      Failed
    else
      let cur := get_current input in
      if fn cur then
        Parsed tt (incr_pos input)
      else
        Failed
.


Definition seq :=
  fun {B}
  (a : input -> result unit)
  (b : input -> result B)
  (input : input) =>
    match a input return (result B) with
      | Failed => Failed
      | Parsed tt input' => b input'
    end
.


Definition seq_l :=
  fun {A}
  (a : input -> result A)
  (b : input -> result unit)
  (input : input) =>
    match a input with
      | Failed as failed => failed
      | Parsed r input' =>
          match b input' with
            | Parsed tt input'' => ret r input''
            | Failed => Failed
          end
    end
.

(* Theorem seq_eq_seq_l :
  forall {A B} (a : input -> result A) (b : input -> result B) (inp : input),
  seq a b inp = seq_l a b inp
.
intros a b inp; compute; t_result; t_unit; reflexivity.
Qed. *)


Definition seq_r :=
  fun {A B}
  (a : input -> result A)
  (b : input -> result B)
  input =>
    match a input with
      | Parsed _ input => b input
      | Failed => Failed
    end
.


Definition seq_n :=
  fun {A B}
  (a : input -> result A)
  (b : input -> result B)
  input =>
    match a input with
      | Failed => Failed
      | Parsed _ input' =>
        match b input' with
          | Parsed _ input'' => Parsed tt input''
          | Failed => Failed
        end
    end
.


Definition seq_b :=
  fun {A B}
  (a : input -> result A)
  (b : input -> result B)
  (input : input) =>
    match a input with
      | Failed => Failed
      | Parsed r1 input' =>
          match b input' with
            | Parsed r2 input'' => Parsed (r1, r2) input''
            | Failed => Failed
          end
    end
.


Definition alt :=
  fun {A} (a : input -> result A) (b : input -> result A) input =>
  match a input with
    | Parsed _ _ as ok => ok
    | Failed => b input
  end
.


Hint Unfold class_sub sub OcamlInt_Arith
            int_Cmp class_le le class_eq
 : unf_oc eq_to_prop.

Ltac unfold_oc :=
 repeat (
  autounfold with unf_oc; auto
 )
.


Definition input_left_nonincr :
  forall A,
  forall (cond : input -> result A),
  forall (p : par _ cond),
  forall i_before,
  match cond i_before with
    | Parsed _ i_after =>
        (input_left i_after <== input_left i_before) = true
    | Failed => True
  end
.
intros.
unfold input_left.
t_result.
unfold_oc.
rewrite <- minus_rev_le.
exact nondecr_input_cond.
Defined.


Hint Unfold input_left_nat input_left : inp.

Theorem input_left_nat_nonincr :
  forall (A : Type),
  forall (cond : input -> result A),
  par A cond ->
  forall (input : input),
  (match cond input with
   | Failed => True
   | Parsed _ input' =>
       input_left_nat input' <= input_left_nat input
   end)
.
autounfold with inp.
intros.
t_result.
unfold_oc.
apply nat_le_of_int; unfold_oc.
apply int_sub_le_zero.
apply input_high_bound.
apply int_sub_le_zero.
rewrite <- input_len_const_input0.
apply input_high_bound.
rewrite <- minus_rev_le.
exact nondecr_input_cond.
Qed.


Require Import Recdef.


Function star
  (A : Type)
  (cond : input -> result A)
  (par0 : par A cond)
  (input1 : input)
  {measure input_left_nat input1}
  :
  result unit
  :=
    let curr_pos := input_pos input1 in
    match cond input1 with
      | Parsed _ input2 =>
          if curr_pos == input_pos input2
          then
            Parsed tt input2
          else
            star A cond par0 input2
      | Failed => Parsed tt input1
    end
.
intros.
pose proof
  (input_left_nat_nonincr A cond par0
     input1)
  as Hnonincr
.
rewrite teq in Hnonincr.
pose proof
  (input_len_const A cond input1)
  as Hconstlen
.
rewrite teq in Hconstlen.

autounfold with unf_oc in teq0.

autounfold with eq_to_prop in teq0.
rewrite int_neq_to_prop in teq0.

pose proof
  (input_pos_of_left input1 input2 Hconstlen)
  as Heqleft.

assert (Hleftnoneq := fun w => teq0 (Heqleft w)).

assert (Hdec := Compare_dec.le_lt_eq_dec
  (input_left_nat input2)
  (input_left_nat input1)
  Hnonincr
).

destruct Hdec. exact l.

apply eq_sym in e.

destruct (Hleftnoneq e).

Defined.

Extraction Inline star_terminate.
Extraction Inline star.

End Kmb_coq.


Extraction "kmb_coq.ml" Kmb_coq.
