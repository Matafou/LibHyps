(* Require Import LibHyps.LibHypsTactics. *)
Require Import LibHyps.Especialize.

(* tests *)
Definition eq_one (i:nat) := i = 1.
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.

Lemma foo: forall x y n m p :nat,
    (forall  (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y n m p H. 
  especialize H at *;[ | | | | | ].
  5: match goal with
       H1 : n < m
         , H2 : n <= m
           , H3 : p > 0
             , H4 : p > 2 |- _ => idtac
     end.
Abort.

Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 

  (* Fail especialize (let x:=not_eq_S in x) with n,m at *. *)
  especialize H at * with n,m,p;[admit|admit|admit|admit| |admit];
  match goal with
    H1 : ?n < ?m
      , H2 : ?n <= ?m
        , H3 : ?p > 0
          , H4 : ?p > 2 |- _ => idtac
  end.
  Undo 1.
  especialize H at 2;
    [ now apply PeanoNat.Nat.lt_le_incl | match goal with | |- False => idtac end;
                                          match type of H with forall (n:_) (m:_) (p:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H at 2 as h;
    [ now apply PeanoNat.Nat.lt_le_incl | match goal with | |- False => idtac end;
                                          match type of h with forall (n:_) (m:_) (p:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H at 2 as ?;
    [ now apply PeanoNat.Nat.lt_le_incl | match goal with | |- False => idtac end;
                                          match type of H_spec_ with forall (n:_) (m:_) (p:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with p;
    [ match goal with | |- False => idtac end; match type of H with forall (n:_) (m:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with n, p;
    [ match goal with | |- False => idtac end; match type of H with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.
  especialize H with p as h;
    [ match goal with | |- False => idtac end; match type of h with forall (n:_) (m:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with n, p as h;
    [ match goal with | |- False => idtac end; match type of h with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.
  especialize H with p as ?;
    [ match goal with | |- False => idtac end; match type of H_spec_ with forall (n:_) (m:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with n, p as ?;
    [ match goal with | |- False => idtac end; match type of H_spec_ with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.

  especialize H at 4 with p;[
      match goal with h: ?n < ?m , h':?n <= ?m, H'':?p > 0 |- ?p > 2 => idtac end
    | match goal with |- False => idtac end; match type of H with forall n m, (n < m) -> _ => idtac end ].
  Undo 1.
  especialize H at 3 with n, p;
    [ match goal with | h: ?n < ?m , h':?n <= ?m |- ?p > 0 => is_evar p end
    | match goal with | |- False => idtac end; match type of H with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.
  especialize H  with p at 3;
    [ match goal with | h: ?n < ?m , h':?n <= ?m |- ?p > 0 => is_evar p end
    | match goal with | |- False => idtac end; match type of H with forall (n:_) (m:_), n < m-> _ => idtac end ].
  Undo 1.
  especialize H with n, p at 3;
    [ match goal with | h: ?n < ?m , h':?n <= ?m |- ?p > 0 => is_evar p end
    | match goal with | |- False => idtac end; match type of H with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.

  especialize H at 2 with p as h2;
    [ match goal with H:?n < ?m |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h2 with forall n m, (n < m) -> _ => idtac end ].
  Undo 1.
  especialize H with p at 2 as h2;
    [ match goal with H:?n < ?m |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h2 with forall n m, (n < m) -> _ => idtac end ].
  Undo 1.
  especialize H at 2 with p as ?;
    [ match goal with H:?n < ?m |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of H_spec_ with forall n m, (n < m) -> _ => idtac end ].
  Undo 1.
  especialize H with p at 2 as ?;
    [ match goal with H:?n < ?m |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of H_spec_ with forall n m, (n < m) -> _ => idtac end ].
  Undo 1.


  especialize H until 2 with p as h ;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h with forall n m, (?q > _) -> _ => idtac end
    ].
  Undo 1.
(* This syntax ("with" before "until") does not work due to "until" not being a keyword. *)
  especialize H with p until 2 as h ;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h with forall n m, (?q > _) -> _ => idtac end
    ].
  Undo 1.
  rename H into Hyp;
  especialize Hyp until 2 with p as ?;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of Hyp_spec_ with forall n m, (?q > _) -> _ => idtac end
    ].
  Undo 1.
  especialize H until 2 as h;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h with forall n m p, (?q > _) -> _ => idtac end ].
  Undo 1.
  rename H into hyp;
  especialize hyp until 2 as ?;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of hyp_spec_ with forall n m p, (?q > _) -> _ => idtac end ].
  Undo 1.
  especialize H until 2;[
      match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of H with forall n m p, (?q > _) -> _ => idtac end ].
  Fail Check h.
  Undo 1.
  especialize H until 3 with n, p;
    [ match goal with | |- ?n < ?m => idtac end
    | match goal with | h: ?n < ?m  |- ?n <= ?m => idtac end
    | match goal with | h: ?n < ?m , h':?n <= ?m |- ?p > 0 => idtac end
    | match goal with | |- False => idtac end].
  Undo 1.


  especialize H at 2, 4 with n, m.
  1: match goal with
       |- ?lft <= ?rght => is_evar lft; is_evar rght
     end.
  2: match goal with
       H: p > 0 , H':?lft <= ?rght |- p > 2 => is_evar lft; is_evar rght
     end.
  3: match goal with
       H: forall p:nat, ?lft < ?rght -> p > 0 -> p > 1 -> _ |- False => is_evar lft; is_evar rght
     end.
  Undo 4.

Abort.




Lemma foo': forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 
  especialize H at 19, 20 with p;[ | | ]; [ 
      (* test generated names *)
      match type of h_premis with
        _> _ => idtac
      end;
      match goal with
        hhh : ?n < ?m, iii : ?n <= ?m |- _ > 2 => idtac
      end
    |  match goal with
         hhh : ?n < ?m, iii : ?n <= ?m |- _ > 1 => idtac
       end
    |  match goal with
       | |- False => idtac
       end ].
  Undo 1.
Abort.


  


Module AS.


  Lemma test_espec: forall x:nat, x = 1 -> (x = 1 -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1 .
    + assumption.
    + match type of h_eqone with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  Lemma test_espec2: forall x:nat, x = 1 -> (x = 1 -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1 as h.
    + assumption.
    + match type of h with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  Lemma test_espec3: forall x:nat, x = 1 -> (x = 1 -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1 as ?.
    + assumption.
    + match type of h_eqone_spec_ with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  Lemma test_espec4: forall x:nat, x = 1 -> (x = 1 -> x = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1, 2 as ?.
    + assumption.
    + reflexivity.
    + match type of h_eqone_spec_ with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  Lemma test_espec5: forall x:nat, x = 1 -> (x = 1 -> x = x -> x = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1, 2, 3 as ?.
    + assumption.
    + reflexivity.
    + reflexivity.
    + match type of h_eqone_spec_ with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.
  
  Lemma test_espec_h: forall x:nat, x = 1 -> (forall a y z:nat, x = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a, y at 1, 2 as h.
    + assumption.
    + reflexivity.
    + exfalso.
      apply h with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.

  Lemma test_espec_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a, y at 1, 2 as ?.
    + reflexivity.
    + reflexivity.
    + exfalso.
      apply h_eqone_spec_ with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  
End AS.


Module Using.

  Lemma test_espec: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y at 1,2 .
    + reflexivity.
    + reflexivity.
    + exfalso.
      apply h_eqone with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  
  Lemma test_espec_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y at 1,2 as h.
    + reflexivity.
    + reflexivity.
    + exfalso.
      apply h with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  
  Lemma test_espec_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y at 1,2 as ?.
    + reflexivity.
    + reflexivity.
    + exfalso.
      apply h_eqone_spec_ with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  

  Lemma test_espec2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y at 2 .
    + reflexivity.
    + exfalso.
      apply h_eqone with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec2_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y at 2 as h.
    + reflexivity.
    + exfalso.
      apply h with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec2_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y at 2 as ?.
    + reflexivity.
    + exfalso.
      apply h_eqone_spec_ with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  

  Lemma test_espec3: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y , z at 2 .
    + reflexivity.
    + exfalso.
      apply h_eqone with 1.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec3_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y , z at 2 as h.
    + reflexivity.
    + exfalso.
      apply h with 1.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec3_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y , z at 2 as ?.
    + reflexivity.
    + exfalso.
      apply h_eqone_spec_ with 1.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  

  Lemma test_espec4: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a, y, z at 1 .
    + reflexivity.
    + exfalso.
      apply h_eqone.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec4_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a, y, z at 1 as h.
    + reflexivity.
    + exfalso.
      apply h.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec4_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a, y, z at 1 as ?.
    + reflexivity.
    + exfalso.
      apply h_eqone_spec_.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  
  Lemma test_espec5: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y,z at 1 .
    + reflexivity.
    + exfalso.
      apply h_eqone.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec5_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y,z at 1 as h.
    + reflexivity.
    + exfalso.
      apply h.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec5_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y,z at 1 as ?.
    + reflexivity.
    + exfalso.
      apply h_eqone_spec_.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  
  Lemma test_espec6: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a at 1 .
    + reflexivity.
    + exfalso.
      apply h_eqone with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec6_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a at 1 as h.
    + reflexivity.
    + exfalso.
      apply h with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec6_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a at 1 as ?.
    + reflexivity.
    + exfalso.
      apply h_eqone_spec_ with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.

  Lemma test_espec7: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,z at 1,4 .
    + reflexivity.
    + rewrite hx.
      instantiate (z:=0).
      reflexivity.
    + exfalso.
      apply h_eqone with 1.
      * reflexivity.
      * reflexivity.
  Qed.

  Lemma test_espec7_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,z at 1,4 as h.
    + reflexivity.
    + rewrite hx.
      instantiate (z:=0).
      reflexivity.
    + exfalso.
      apply h with 1.
      * reflexivity.
      * reflexivity.
  Qed.
  Lemma test_espec7_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,z at 1,4 as ?.
    + reflexivity.
    + rewrite hx.
      instantiate (z:=0).
      reflexivity.
    + exfalso.
      apply h_eqone_spec_ with 1.
      * reflexivity.
      * reflexivity.
  Qed.

(* This tests only hold for coq >= 8.18 *)
(*
  Lemma test_espec8: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone with a at 1,4 .
  Abort.

  Lemma test_espec8_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone with a at 1,4 as h.
  Abort.

  Lemma test_espec8_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone with a at 1,4 as ?.
  Abort.

  Lemma test_espec9: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone at 1,4.
  Abort.

  Lemma test_espec9_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone at 1,4 as h.
  Abort.

  Lemma test_espec9_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone at 1,4 as ?.
  Abort.
*)
End Using.


Lemma test_esepec_6_7: (eq_one 2 -> eq_one 3 ->eq_one 4 ->eq_one 5 ->eq_one 6 ->eq_one 7 ->eq_one 8 -> eq_one 9 -> eq_one 1 -> False) -> True.
Proof.
  intros H.
  especialize H at 1,2,3,4,5,7 as h; [ admit | admit | admit  | admit | admit | admit | ];
  match type of h with
    eq_one 7 -> eq_one 9 -> eq_one 1 -> False => idtac
  end.
  Undo.
  especialize H at 1,2,3,4,5,7,9 as h; [ admit | admit | admit  | admit | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> False => idtac end].
  Undo.
  exact I.
Qed.


Axiom ex_hyp : (forall (b:bool), forall x: nat, eq_one 1 -> forall y:nat, eq_one 2 ->eq_one 3 ->eq_one 4 ->eq_one x ->eq_one 6 ->eq_one y -> eq_one 8 -> eq_one 9 -> False).

Lemma test_esepec: True.
Proof.
  (* specialize ex_hyp as h. *)
  (* especialize ex_hyp at 2 as h. *)

  especialize ex_hyp at 3 with b,x,y as h;[ ..  | match type of h with eq_one 1 -> eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) at 2 as h;[ .. | match type of h with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) at 2,3 as h;[  .. | match type of h with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  Fail especialize H at 2,3,5 as h. 
  Undo.
  especialize (ex_hyp true) with x at 2,3,5 as h ;[ ..  | match type of h with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) with x at 2,3,5,6 as h ;[ ..  | match type of h with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  Fail especialize H with x at 2,3,5,7 as h.
  especialize (ex_hyp true) with x,y at 2,3,5,7 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) with x,y at 2,3,5,7,9 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) with x,y at 2,3,5,7,8,9 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) at 2 as ?;[ .. | match type of H_spec_ with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) at 2,3 as ?;[  .. | match type of H_spec_ with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  Fail especialize H at 2,3,5 as ?. 
  Undo.
  especialize (ex_hyp true) with x at 2,3,5 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) with x at 2,3,5,6 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) with x at 3,2,5,6 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  Fail especialize H with x at 2,3,5,7 as ?.
  especialize (ex_hyp true) with x,y at 2,3,5,7 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) with x,y at 2,3,5,7,9 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) with x,y at 1,2,3,5,7,9 as ?;[ ..  | match type of H_spec_ with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize (ex_hyp true) with x,y at 2,3,5,7,8,9 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac end].
  Undo.

  (* when the argument is not a hyptothesis we must give a name.*)
  Fail especialize (ex_hyp true) at 2.

  Undo.
  generalize (ex_hyp true) as H.
  intro.
  especialize H at 2 as h;[ .. | match type of h with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H at 2,3 as h;[  .. | match type of h with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H at 2,3,5 as h.  *)
  especialize H with x at 2,3,5 as h ;[ ..  | match type of h with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H with x at 2,3,5,6 as h ;[ ..  | match type of h with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H with x at 2,3,5,7 as h. *)
  especialize H with x,y at 2,3,5,7 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H with x,y at 2,3,5,7,9 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize H with x,y at 1,2,3,5,7,9 as h ;[ ..  | match type of h with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize H with x,y at 2,3,5,7,8,9 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac end].
  Undo.

  especialize H at 2 as ?;[ .. | match type of H_spec_ with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H at 2,3 as ?;[  .. | match type of H_spec_ with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H at 2,3,5 as ?.  *)
  especialize H with x at 2,3,5 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H with x at 2,3,5,6 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H with x at 2,3,5,7 as ?. *)
  especialize H with x,y at 2,3,5,7 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H with x,y at 2,3,5,7,9 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize H with x,y at 1,2,3,5,7,9 as ? ;[ ..  | match type of H_spec_ with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize H with x,y at 2,3,5,7,8,9 as ? ;[ ..  | match type of H_spec_ with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac end].
  Undo.

  especialize H at 2;[ .. | match type of H with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H at 2,3;[  .. | match type of H with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H at 2,3,5.  *)
  especialize H with x at 2,3,5 ;[ ..  | match type of H with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H with x at 2,3,5,6 ;[ ..  | match type of H with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H with x at 2,3,5,7. *)
  especialize H with x,y at 2,3,5,7 ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
  especialize H with x,y at 2,3,5,7,9 ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize H with x,y at 1,2,3,5,7,9 ;[ ..  | match type of H with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac end].
  Undo.
  especialize H with x,y at 2,3,5,7,8,9 ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac end].
  Undo.
  especialize H with x,y at 8,2,3,5,7,9 ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac end].
  Undo.

  exact I.
Qed.



Lemma test_espec_namings: forall n:nat, (eq_one n -> eq_one 1 -> False) -> True.
Proof.
  intros n h_eqone.
  (* especialize PeanOant.Nat.quadmul_le_squareadd with a at 1 as hh : h. *)
  especialize PeanoNat.Nat.quadmul_le_squareadd with a at 1 as hh.
  { apply le_n. }
  especialize min_l with n,m at 1 as ?.
  { apply (le_n O). }
  especialize h_eqone at 2 as h1.
  { reflexivity. }
  unfold eq_one in min_l_spec_.
  (* match type of h2 with 1 = 1 => idtac | _ => fail end. *)
  match type of h1 with eq_one n -> False => idtac | _ => fail end.
  exact I.
Qed.


(* "until i" and "at *" *)

Lemma test_esepec_until_star: (eq_one 2 -> eq_one 3 ->eq_one 4 ->eq_one 5 ->eq_one 6 ->eq_one 7 ->eq_one 8 -> eq_one 9 -> eq_one 1 -> False) -> True.
Proof.
  
  intros h_eqone.
  (* specialize on term ==> create a new hyp *)
  (* if arg not a hyp then "as" is mandatory *)
  Fail especialize (let x:=not_eq_S in x) with n,m at *.
  Undo.
  especialize (let x:=not_eq_S in x) with n,m at * as h;
    [ .. | match type of h with (S _)<>(S _) => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:=not_eq_S in x) with n,m until 1 as ?;
    [ .. | match type of H_spec_ with (S _)<>(S _) => idtac | _ => fail "Test failed!" end].
 Undo.
 (* name mandatory *)
 Fail especialize (let x:=not_eq_S in x) with n,m until 1.
 Undo.
  especialize (let x:=not_eq_S in x) with n,m at * as h;
    [ .. | match type of h with (S _)<>(S _) => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:=PeanoNat.Nat.add_sub_eq_nz in x) with n,m,p until 2 as h;
    [ .. | match type of h with ?m + ?p = ?n => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:= PeanoNat.Nat.add_sub_eq_nz in x) with p until 1 as h;
    [ .. | match type of h with forall n m : nat, n - m = ?p -> m + ?p = n => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:=h_eqone in x) at * as ? ;
    [ ..  | match type of H_spec_ with False => idtac | _ => fail "Test failed!" end].
  Undo.
  (* proveprem_until h_eqone 4. *)
  especialize (let x:= h_eqone in x) until 4 as ? ;
    [ admit |admit |admit |admit | match type of H_spec_ with eq_one 6 -> eq_one 7 -> eq_one 8 -> eq_one 9 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end ].
  Undo.
  (* behavior when acting on a hypothesis: replace the hyp by its specialize version *)
  especialize h_eqone until 4;
    [ admit | admit |admit |admit | ];
  match type of h_eqone with eq_one 6 -> eq_one 7 -> eq_one 8 -> eq_one 9 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end.
  Undo.
  especialize h_eqone at * ;
    [ .. | match type of h_eqone with False => idtac | _ => fail "Test failed!" end].
  Undo.
  (* unless we give the "as" option *)
  especialize h_eqone at * as h;
    [ admit |admit |admit |admit |admit |admit |admit |admit |admit | match type of h with False => idtac | _ => fail "Test failed!" end;
                                                                      match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 4 -> eq_one 5 -> eq_one 6 -> eq_one 7 -> eq_one 8 -> eq_one 9 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone until 4 as h;
    [ admit |admit |admit |admit | match type of h with eq_one 6 -> eq_one 7 -> eq_one 8 -> eq_one 9 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  exact I.
Qed.

