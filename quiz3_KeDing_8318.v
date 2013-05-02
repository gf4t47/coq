(** **** KE DING 8318 *)

Require Export Poly. (* Just for definitions, not homework *)
(** **** Quiz #3 
   Define a Coq polymorphic list function called 
   "shuffle" which alternates the elements
   of two lists in the resulting output list
   e.g., 
   (shuffle [true] [false,false]) ==> [true,false,false]
   (shuffle [false,false] [true]) ==> [false,true,false]
   (shuffle [1,2,3] [10,11,12,13,14]) ==> [1,10,2,11,3,12,13,14]
   (shuffle [10,11,12,13,14] [1,2,3]) ==> [10,1,11,2,12,3,13,14]
   (shuffle [] [1,2]) ==> [1,2]
   (shuffle [1,2] []) ==> [1,2]

    Also devise a test or two for your function
*)

(* definition here *)
Fixpoint shuffle {X : Type} (l1 : list X) (l2 : list X) : list X :=
  match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | x1::t1, x2::t2 => x1::x2::(shuffle t1 t2)
  end.

Example test1 : shuffle [true] [false,false] = [true,false,false].
Proof. reflexivity. Qed.
Example test2 : shuffle [false,false] [true] = [false,true,false].
Proof. reflexivity. Qed.
Example test3 : shuffle [1,2,3] [10,11,12,13,14] = [1,10,2,11,3,12,13,14].
Proof. reflexivity. Qed.
Example test4 : shuffle [10,11,12,13,14] [1,2,3] = [10,1,11,2,12,3,13,14].
Proof. reflexivity. Qed.
Example test5 : shuffle [] [1,2] = [1,2].
Proof. reflexivity. Qed.
Example test6 : shuffle [1,2] [] = [1,2].
Proof. reflexivity. Qed.

(* tests here *)
Example devise_test1 : shuffle ["c", "l", "o", "y", "pomona"] ["a", "p","l"]
                     = ["c", "a", "l", "p", "o", "l", "y", "pomona"].
Proof. reflexivity. Qed.
Example devise_test2 : shuffle [monday,wednesday,friday,sunday] [tuesday,thursday,saturday] 
                     = [monday,tuesday,wednesday,thursday,friday,saturday,sunday].
Proof. reflexivity. Qed.
Example devise_test3 : shuffle [add o, add o, add o, add (dub o), dub (add o)] [dub o, dub o]
                     = [add o, dub o, add o, dub o, add o, add (dub o), dub (add o)].
Proof. reflexivity. Qed.
Example devise_test4 : @shuffle nat [] [] = [].
Proof. reflexivity. Qed.

(* email answers .v file to jrfisher@csupomona.edu, using quiz3 in subject line *)

(** **** KE DING 8318 *)