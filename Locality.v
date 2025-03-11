(** Hrishee S *)
(** Locality.v *)

(** Import machinery to work with nats, bools, and lists *)
Require Import Arith.
Require Import Peano.
Require Import Bool.
Require Import List.
Import ListNotations.

Require Import Lia.

Open Scope nat_scope.
Open Scope bool_scope.


(* We use a list of bools as our representation of a bitstring *)

Definition bin := list bool.

(* Miscellaneous properties of natural numbers *)

Lemma mul_2_l : forall n : nat, 2 * n = n + n .
Proof.
    lia.
Qed.

Lemma divide_both_sides_by_2 : forall n m: nat, 2 * n = 2 * m <-> n = m.
Proof.
    lia. 
Qed.

Lemma list_len_preserved : forall (i : nat) (a : bool) (b : bin),
  S i < length (a :: b) -> i < length b.
Proof. 
  intros i a b H.
  rewrite Nat.succ_lt_mono.
  simpl in H. assumption.
Qed.

Lemma nonzero_nat_minus_one_plus_one : forall (n : nat),
    n > 0 -> n - 1 + 1 = n.
Proof.
    intros.
    destruct n eqn:Hn.
    - inversion H.
    - lia.
Qed.

(* Definition and properties of absolute differences *)

Definition abs_diff (a b : nat) : nat :=
    if Nat.leb b a then a - b else b - a.

Example test_abs_diff_1 :
    abs_diff 2 3 = 1.
Proof. simpl. reflexivity. Qed.

Example test_abs_diff_2 :
    abs_diff 3 2 = 1.
Proof. simpl. reflexivity. Qed.

Example test_abs_diff_3 :
    abs_diff 0 0 = 0.
Proof. simpl. reflexivity. Qed.

Lemma abs_diff_plus_1_r :
    forall (a : nat), abs_diff (a) (a + 1) = 1.
Proof.
    intros.
    unfold abs_diff.  
    destruct (a + 1 <=? a) eqn:H.
    - apply Nat.leb_le in H. 
      lia.
    - lia.
Qed. 

Lemma abs_diff_plus_1_l:
    forall (a : nat), abs_diff (a + 1) (a) = 1.
Proof. 
    intros.
    unfold abs_diff.  
    destruct (a <=? a + 1) eqn:H.
    - lia.
    - apply Nat.leb_gt in H. lia.
Qed.  

Lemma abs_diff_reduce :
    forall (a b c: nat), abs_diff (a + c) (b + c) = abs_diff a b.
Proof.
    intros.
    unfold abs_diff.
    destruct (b + c <=? a + c) eqn:H.
    - destruct (b <=? a) eqn:H2.
        + lia.
        + apply Nat.leb_gt in H2.
          apply Nat.leb_le in H.
          lia.
    - destruct (b <=? a) eqn:H2.
        + apply Nat.leb_gt in H.
          apply Nat.leb_le in H2.
          lia.
        + lia.
Qed.              


Lemma abs_diff_multiply_by_2 :
    forall (a b : nat), abs_diff (2 * a) (2 * b) = 2 * abs_diff a b.
Proof. 
    intros.
    unfold abs_diff.
    destruct (2 * b <=? 2 * a) eqn:H; rewrite <- Nat.mul_sub_distr_l.
    - destruct (b <=? a) eqn:H2. 
        + reflexivity. 
        + apply Nat.leb_gt in H2.
          apply Nat.leb_le in H.
          lia.
    - destruct (b <=? a) eqn:H2.
        + apply Nat.leb_gt in H.
          apply Nat.leb_le in H2.
          lia. 
        + lia. 
Qed.   


(* Definition and Properties of exponentiation *)

Fixpoint exp (base power : nat) : nat :=
    match power with
    | 0 => 1
    | S p => base * (exp base p)
    end.

Example test_exp_1 : 
    exp 2 3 = 8.
Proof. simpl. reflexivity. Qed.

Example test_exp_2 : 
    exp 2 1 = 2.
Proof. simpl. reflexivity. Qed.

Example test_exp_3 : 
    exp 1 0 = 1.
Proof. simpl. reflexivity. Qed.

Example test_exp_4 : 
    exp 0 2 = 0.
Proof. simpl. reflexivity. Qed.

Theorem exponent_increment_rule_for_base_2 :
    forall (p : nat),
        2 * exp 2 p = exp 2 (p + 1).
Proof.
    intros.
    induction p. 
    - simpl. reflexivity.
    - simpl. lia.
Qed.


(* Defining single-bit flips of a bitstring *)

Fixpoint flip_bit (m:bin) (i:nat): bin :=
    match m, i with
    | [], _ => []
    | b :: l', 0 => negb b :: l'
    | b :: l', S n' => b :: flip_bit l' n'
    end.

Example test_flip_bit_1 :
    flip_bit [false] 0 = [true].
Proof. simpl. reflexivity. Qed.

Example test_flip_bit_2 :
    flip_bit [false;true] 1 = [false;false].
Proof. simpl. reflexivity. Qed.

Example test_flip_bit_out_bounds :
    flip_bit [false;true] 3 = [false;true].
Proof. simpl. reflexivity. Qed.

Example test_flip_bit_middle :
    flip_bit [false;true;false;false;true;true] 3 = [false;true;false;true;true;true].
Proof. simpl. reflexivity. Qed.

Example test_flip_bit_empty :
    flip_bit [] 0 = [].
Proof. simpl. reflexivity. Qed.


(* Standard Binary code definition *)

Fixpoint standard_bin_to_nat (m:bin) : nat :=
  match m with 
  | [] => 0
  | true :: l' => (2 * (standard_bin_to_nat l')) + 1
  | false :: l' => 2 * (standard_bin_to_nat l')
  end.

Example test_standard_bin_to_nat_empty_is_0 :
  standard_bin_to_nat [] = 0.
Proof. simpl. reflexivity.  Qed.

Example test_standard_bin_to_nat_0s_is_0 :
  standard_bin_to_nat [false;false] = 0.
Proof. simpl. reflexivity.  Qed.

Example test_standard_bin_to_nat_10_is_2 :
    standard_bin_to_nat [false;true] = 2.
Proof. simpl. reflexivity.  Qed.

Example test_standard_bin_to_nat_1_is_1 :
    standard_bin_to_nat [true] = 1.
Proof. simpl. reflexivity.  Qed.


(* Functions and Theorems about enumerating all length n bitstrings*)

Fixpoint all_bitstrings_of_length_n (n : nat) : list bin :=
  match n with
  | 0 => [[]] 
  | S n' => map (fun bs : bin => false :: bs) (all_bitstrings_of_length_n n')
            ++ (map (fun bs : bin => true :: bs) (all_bitstrings_of_length_n n'))
  end.

Example test_all_bitstrings_of_length_n_0 :
    all_bitstrings_of_length_n 0 = [[]].
Proof. simpl. reflexivity. Qed.

Example test_all_bitstrings_of_length_n_1 :
    all_bitstrings_of_length_n 1 = [[false]; [true]].
Proof. simpl. reflexivity. Qed.

Example test_all_bitstrings_of_length_n_2 :
    all_bitstrings_of_length_n 2 = [[false;false]; [false;true]; [true;false]; [true;true]].
Proof. simpl. reflexivity. Qed.

Example test_all_bitstrings_of_length_n_3 :
    all_bitstrings_of_length_n 3 = [[false; false; false]; [false; false; true];
                                    [false; true; false]; [false; true; true];
                                    [true; false; false]; [true; false; true];
                                    [true; true; false]; [true; true; true]].
Proof. simpl. reflexivity. Qed.

(* Here we prove some correctness lemmas about this enumeration function
   that will come in handy later. *)

(* Lemma that states that enumerating all bitstrings of length n results in 2 ^ n bitstrings*)
Lemma num_bitstrings_of_length_n_is_exp2n :
    forall (n : nat),
        length (all_bitstrings_of_length_n n) = exp 2 n. 
Proof.
    intros. induction n. 
    -  simpl. reflexivity.
    -  simpl. 
       rewrite app_length.
       repeat rewrite map_length.
       rewrite IHn. 
       lia.
Qed.

(* Lemma that states that if a bitstring is in all_bitstrings_of_length_n n,
    it must have length n *)
Lemma enumerated_bitstring_has_length_n : 
    forall (n : nat) (b : bin), 
    In b (all_bitstrings_of_length_n n) -> length b = n.
Proof.
    intros n.
    induction n as [|n' IHn'].
    - intros. simpl in H. 
      destruct b; destruct H; try contradiction.
      reflexivity. rewrite <- H. reflexivity. 
    - intros b H. simpl in H.
      apply in_app_or in H.
      destruct H as [HFT | HFT];
        apply in_map_iff in HFT;
        destruct HFT as [b' [Hb' Hb]];
        rewrite <- Hb';
        simpl;
        apply IHn' in Hb;
        rewrite Hb;
        reflexivity.
Qed.

(* *************************************************************** *)
(* Here, we copy All and All_In from Logic2 in Software Foundations *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
    match l with
    | [] => True
    | x :: l' => P x /\ All P l'
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  split. 
  - (* -> *) induction l as [|x l' IHl'].
    + simpl. intros HFalse. apply I. (* I tactic resolves True. *)
    + simpl. intros H. split.
        apply H. left. reflexivity.
        apply IHl'. intros x0 H0. apply H. right. apply H0.
  - (* <- *) induction l as [| x l' IHl'].
    + simpl. intros HTrue x HFalse. destruct HFalse.
    + simpl. intros [HPx HAll] x0 [Hxx0 | HIn].
        rewrite <- Hxx0. apply HPx.
        apply IHl' in HIn. apply HIn. apply HAll.
Qed.
(* *************************************************************** *)


Definition all_b_in_bs_have_length (n : nat) (bs : list bin): Prop := 
    All (fun b => length b = n) bs.


(* Main correctness theorem : all bitstrings generated as a result of our
  all_bitstrings_of_length_n function have length n *)
Theorem all_enumerated_bitstrings_have_length_n :
    forall (n : nat),
        all_b_in_bs_have_length n (all_bitstrings_of_length_n n).
Proof.
    intros.
    apply All_In.
    apply enumerated_bitstring_has_length_n.
Qed. 


(* First result -- Proving that flipping the ith bit of a 
standard binary bitstring results in an absolute difference 
of 2^i  *)

(* A quick example. *)
Example standard_bin_bitflip_difference_example :
    abs_diff (standard_bin_to_nat (flip_bit [false;false;false;true] 2)) 
             (standard_bin_to_nat [false;false;false;true]) 
             = exp 2 2.
Proof. simpl. reflexivity. Qed.

(* The theorem. *)
Theorem flipping_ith_bit_difference_standard_binary :
    forall (b : bin) (i : nat), 
        i < length b -> abs_diff (standard_bin_to_nat (flip_bit b i))
                                    (standard_bin_to_nat b)
                          = exp 2 i.
Proof.
    (** We proceed by double induction on b (the list) 
        and i (the index of the bit we flip)**)
    intros b. induction b. 
    - (** Base cases. b = [], i = 0 **)
       intros i. induction i; intros H; inversion H.
    -  intros i H. induction i.
        + (** b = a :: b', i = 0 **) 
           simpl. destruct a; simpl; repeat rewrite Nat.add_0_r.
            * apply abs_diff_plus_1_r.
            * apply abs_diff_plus_1_l.
        + (** b = a :: b', i = S i' **)
          simpl. 
          destruct a; simpl;
          repeat rewrite Nat.add_0_r;
          try (rewrite abs_diff_reduce);
          repeat rewrite <- mul_2_l;
          rewrite abs_diff_multiply_by_2;
          rewrite divide_both_sides_by_2;
          apply IHb.
            * apply list_len_preserved with (a := true).
              apply H.
            * apply list_len_preserved with (a := false).
              apply H.
Qed.

(** Our next result: We want to show that, for a fixed standard binary 
     bitstring 's', the sum total of absolute differences elicited 
     from flipping each bit is 
        \sum_{i = 0}^{length(s)-1} 2^i = 2^(length s) - 1 *)

(* Some definitions to help with this. *)

(* First, we define "inner point locality" to be, for a fixed bitstring 'b',
   the sum total of absolute differences between b and each other bitstring that is a single bit-flip apart. 
   We write the definition in such a way that the type of binary representation is a
   parameter to stay faithful to the original definition in the paper.

   Note that i, the index of the bitstring we sum up to,
   is also given as a parameter here. But that is only to assist in 
   the recursive computation. In the definition of inner point locality, 
   i otherwise starts at the length of the bitstring minus 1. 
   (there might be a better way to do this in Coq that I'm not familiar with)
*)
Fixpoint inner_point_locality (repr : bin -> nat) (b : bin) (i : nat) : nat :=
  match i with
  | 0 => abs_diff (repr (flip_bit b 0)) (repr b)
  | S i' => abs_diff (repr (flip_bit b i))
                     (repr b) + inner_point_locality repr b i'
  end.

Example inner_point_locality_1111_standard_binary :
    inner_point_locality (standard_bin_to_nat) ([true;true;true;true]) 3
        = abs_diff (standard_bin_to_nat [true;true;true;true]) (standard_bin_to_nat [false;true;true;true])
          + abs_diff (standard_bin_to_nat [true;true;true;true]) (standard_bin_to_nat [true;false;true;true])
          + abs_diff (standard_bin_to_nat [true;true;true;true]) (standard_bin_to_nat [true;true;false;true])
          + abs_diff (standard_bin_to_nat [true;true;true;true]) (standard_bin_to_nat [true;true;true;false]).
Proof.
    simpl. reflexivity.
Qed. 

(* To show a connection to the geometric series with common ratio 2,
     we define a the following *)
Fixpoint sum_powers_of_2_from_0_to_n (n : nat) : nat :=
  match n with
  | 0 => exp 2 0
  | S n' => (exp 2 n) + sum_powers_of_2_from_0_to_n n'
  end.

Example sum_powers_of_2_from_0_to_n_1 : 
    sum_powers_of_2_from_0_to_n 0 = exp 2 0.
Proof. simpl. reflexivity. Qed.

Example sum_powers_of_2_from_0_to_n_2 : 
    sum_powers_of_2_from_0_to_n 1 = exp 2 0 + exp 2 1.
Proof. simpl. reflexivity. Qed.

Example sum_powers_of_2_from_0_to_n_3 : 
    sum_powers_of_2_from_0_to_n 4 = exp 2 0 + exp 2 1 + exp 2 2 + exp 2 3 + exp 2 4.
Proof. simpl. reflexivity. Qed.

(* The closed form for the
   geometric series. *)
Lemma sum_powers_of_2_from_0_to_n_closed_form :
    forall (n : nat),
        sum_powers_of_2_from_0_to_n n = (exp 2 (n + 1)) - 1.
Proof.
    intros. induction n. 
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHn.
      repeat rewrite Nat.add_0_r.
      rewrite <- mul_2_l.
      rewrite exponent_increment_rule_for_base_2.
      lia.
Qed.


(* The theorems for inner point locality for standard binary. *)

(*
    We start with a helper theorem parameterized by i.
*)
Theorem inner_point_locality_closed_form_standard_binary_parametrized_by_i :
    forall (b : bin) (i : nat), 
        i < length b -> 
        inner_point_locality (standard_bin_to_nat) b i = (exp 2 (i + 1)) - 1. 
Proof.
    (** We proceed by double induction on b (the list) 
    and i (the index of the bitstring we calculate inner point locality up to)**)
    intros b.
    induction b.
    - intros i. induction i; intros H; inversion H.
    - intros i H. induction i.
        + simpl. destruct a.
            * simpl. rewrite Nat.add_0_r. rewrite abs_diff_plus_1_r. reflexivity.
            * simpl. rewrite Nat.add_0_r. rewrite abs_diff_plus_1_l. reflexivity.
        + simpl.
          destruct a; simpl;
          repeat rewrite Nat.add_0_r;     
          repeat rewrite <- mul_2_l;
          try (rewrite abs_diff_reduce);
          rewrite abs_diff_multiply_by_2;
          rewrite flipping_ith_bit_difference_standard_binary.
            * rewrite IHi.
              rewrite exponent_increment_rule_for_base_2.
              lia.
              apply Nat.lt_succ_l; assumption.
            * apply list_len_preserved with (a := true); assumption.
            * rewrite IHi.
              rewrite exponent_increment_rule_for_base_2.
              lia.
              apply Nat.lt_succ_l; assumption.
            * apply list_len_preserved with (a := false); assumption.
Qed.

(*
    The actual theorem with i = (length b) - 1. 
*)
Theorem inner_point_locality_closed_form_standard_binary :
    forall (b : bin), 
        length b > 0 -> 
        inner_point_locality (standard_bin_to_nat) b ((length b) - 1) = (exp 2 (length b)) - 1. 
Proof.
    intros.
    specialize (inner_point_locality_closed_form_standard_binary_parametrized_by_i b (length b - 1)) as Hparam.
    rewrite nonzero_nat_minus_one_plus_one with (n := length b) in Hparam.
    apply Hparam.
    lia.
    assumption.
Qed.

(* A straightforward corollary, showing the connection to the geometric series defined earlier. *)

Corollary inner_point_locality_standard_binary_is_geometric_series :
    forall (b : bin),
        length b > 0 ->
        inner_point_locality (standard_bin_to_nat) b ((length b) - 1) = sum_powers_of_2_from_0_to_n ((length b) - 1).
Proof.
    intros.
    rewrite sum_powers_of_2_from_0_to_n_closed_form.
    rewrite nonzero_nat_minus_one_plus_one with (n := length b).
    apply inner_point_locality_closed_form_standard_binary; assumption.
    assumption.
Qed.

(* Next, we define "point locality" for a representation of a given length n
to be the total sum of inner point locality for every length n bitstring  
under a given representation (in our case, standard binary). *)

Fixpoint point_locality (repr : bin -> nat) (all_bitstrings : list bin) : nat :=
  match all_bitstrings with
  | [] => 0 
  | b :: l' => inner_point_locality (repr) b ((length b) - 1) + point_locality (repr) l'
  end.

Example point_locality_length_0 :
    point_locality (standard_bin_to_nat) (all_bitstrings_of_length_n 0) = 0.
Proof.
    simpl. reflexivity.
Qed.

Example point_locality_length_3_standard_binary :
    point_locality (standard_bin_to_nat) (all_bitstrings_of_length_n 3)
        = inner_point_locality (standard_bin_to_nat) [true;true;true] (3 - 1)
          + inner_point_locality (standard_bin_to_nat) [false;true;true] (3 - 1)
          + inner_point_locality (standard_bin_to_nat) [true;false;true] (3 - 1)
          + inner_point_locality (standard_bin_to_nat) [true;true;false] (3 - 1)
          + inner_point_locality (standard_bin_to_nat) [true;false;false] (3 - 1)
          + inner_point_locality (standard_bin_to_nat) [false;true;false] (3 - 1)
          + inner_point_locality (standard_bin_to_nat) [false;false;true] (3 - 1)
          + inner_point_locality (standard_bin_to_nat) [false;false;false] (3 - 1).
Proof.
    simpl. reflexivity.
Qed. 

(* Now, onto our main result: *)

(* Here we state a helper theorem that states that if all binary strings in a list 
    of binary strings are the same length, then computing point locality for standard
    binary on that list reduces to a closed form *)
Theorem point_locality_standard_binary_only_depends_on_length_of_bitstrings :
    forall (bs : list bin) (n : nat),
        n > 0 ->
        all_b_in_bs_have_length n bs-> 
            point_locality (standard_bin_to_nat) (bs) 
            = (length bs) * ((exp 2 n) - 1).
Proof.
    intros bs n Hn Hlen.
    induction bs.
    - simpl. reflexivity.
    - simpl. 
      rewrite IHbs.
      + rewrite inner_point_locality_closed_form_standard_binary;
        destruct Hlen as [Hlena Hlenbs];
        rewrite Hlena.
            * reflexivity.
            * apply Hn.  
      + destruct Hlen as [Hlena Hlenbs].
        apply Hlenbs.
Qed.


(* Now, we prove our main theorem: A closed form for point locality for standard binary *)

Theorem point_locality_closed_form_standard_binary :
    forall (n : nat),
        n > 0 -> 
            point_locality (standard_bin_to_nat) (all_bitstrings_of_length_n n) 
            = (exp 2 n) * ((exp 2 n) - 1).
Proof.
    intros n Hn.
    rewrite point_locality_standard_binary_only_depends_on_length_of_bitstrings with 
        (bs := all_bitstrings_of_length_n n) (n := n); try assumption.
    - rewrite num_bitstrings_of_length_n_is_exp2n. 
      reflexivity.
    - apply all_enumerated_bitstrings_have_length_n.
Qed.

     




