open Logic.Verifier

module Axioms = struct
  let member = make_builtin ~arity:2 ~name:"member"
  let member x y = apply member [x; y]
  let equal = make_builtin ~arity:2 ~name:"equal"
  let equal x y = apply equal [x; y]

  let extensionality =
    forall ~name:"a" (fun a -> forall ~name:"b" (fun b -> implies (forall ~name:"x" (fun x -> iff (member x a) (member x b))) (equal a b)))
  let substitution =
    forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> forall2 ~arity:1 ~name:"p" (fun p -> implies (equal x y) (iff (apply p [x]) (apply p [y])))))
  let pair =
    forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> exists ~name:"z" (fun z -> forall ~name:"a" (fun a -> iff (member a z) (or_ (equal a x) (equal a y))))))
  let union =
    forall ~name:"a" (fun a -> exists ~name:"z" (fun z -> forall ~name:"x" (fun x -> iff (member x z) (exists ~name:"y" (fun y -> and_ (member x y) (member y a))))))
  let regularity =
    forall ~name:"a" (fun a -> implies (exists ~name:"x" (fun x -> member x a)) (exists ~name:"y" (fun y -> and_ (member y a) (not_ (exists ~name:"z" (fun z -> and_ (member z a) (member z y)))))))
  let replacement =
    forall ~name:"a" (fun a -> forall2 ~arity:2 ~name:"P" (fun p -> implies (forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> forall ~name:"z" (fun z -> implies (and_ (apply p [x; y]) (apply p [x; z])) (equal y z)))))
      (exists ~name:"b" (fun b -> forall ~name:"x" (fun x -> iff (member x b) (exists ~name:"y" (fun y -> and_ (member y a) (apply p [x; y]))))))))

  let subset = predicate_of_formula ~arity:2 ~name:"subset" (function [x; y] -> forall ~name:"x" (fun a -> (implies (member a x) (member a y))) | _ -> failwith "")

  (* let tarski =
    forall ~name:"n" (fun n -> exists ~name:"m" (fun m ->
      and_ (member n m)
      (and_ (forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> implies (and_ (member x m) (apply subset [y; x])) (member y m))))
      (forall ~name:"x" (fun x -> implies (member x m) (exists ~name:"z" (fun z -> (and_ (member z m) (forall ~name:"y" (fun y -> implies (apply subset [y; x]) (member y z))))))))))) *)
end

module Fun1 = struct
  let existence pred =
    forall ~name:"x" (fun x -> exists ~name:"a" (fun a -> apply pred [x; a]))

  let uniqueness pred =
    forall ~name:"x" (fun x -> forall ~name:"a" (fun a -> forall ~name:"b" (fun b ->
      implies (and_ (apply pred [x; a]) (apply pred [x; b])) (Axioms.equal a b))))
end

module Singleton = struct
  let pred = predicate_of_formula ~arity:2 ~name:"singleton" (function [x; a] -> forall ~name:"z" (fun z -> iff (Axioms.member z a) (Axioms.equal z x)) | _ -> failwith "")

  let exists_proof = (let pair = assertion Axioms.pair in
    let m_p = consequence [pattern_implies (metavar 1) (metavar 2); metavar 1] (metavar 2) in
    let remove_dup = consequence [pattern_iff (metavar 1) (pattern_or (metavar 2) (metavar 2))] (pattern_iff (metavar 1) (metavar 2)) in
    intro_forall ~name:"x" (fun x ->
      let pair_1 = elim_forall x (elim_forall x pair) in
      let pair_1_implies_sing = inst_exists (judgement_conclusion pair_1) (fun the_set pair_property ->
        intro_exists the_set
          (intro_forall ~name:"a" (fun a ->
            infer remove_dup
              [elim_forall a pair_property]
              (iff (Axioms.member a the_set) (Axioms.equal a x))))) in
      infer m_p [pair_1_implies_sing; pair_1] (exists ~name:"a" (fun a -> apply pred [x; a]))))

  let unique_proof = (let ext = assertion Axioms.extensionality in
    intro_forall ~name:"x" (fun x -> intro_forall ~name:"a" (fun a -> intro_forall ~name:"b" (fun b -> 
      assuming (and_ (apply pred [x; a]) (apply pred [x; b])) (fun assumptions ->
        let conj_1 = consequence [pattern_and (metavar 1) (metavar 2)] (metavar 1) in
        let conj_2 = consequence [pattern_and (metavar 1) (metavar 2)] (metavar 2) in
        let iff_trans = consequence [pattern_iff (metavar 1) (metavar 3); pattern_iff (metavar 2) (metavar 3)] (pattern_iff (metavar 1) (metavar 2)) in
        let m_p = consequence [pattern_implies (metavar 1) (metavar 2); metavar 1] (metavar 2) in
        let a_sing_x = infer conj_1 [assumptions] (apply pred [x; a]) in
        let b_sing_x = infer conj_2 [assumptions] (apply pred [x; b]) in
        let same_members = intro_forall ~name:"z" (fun z ->
          infer iff_trans [elim_forall z a_sing_x; elim_forall z b_sing_x] (iff (Axioms.member z a) (Axioms.member z b))) in
        infer m_p [elim_forall b (elim_forall a ext); same_members] (Axioms.equal a b))))))
end

let verify proof claim =
  let allowed_axioms = [Axioms.extensionality; Axioms.substitution; Axioms.pair; Axioms.union; Axioms.regularity; Axioms.replacement] in
  assert (equal_formula (judgement_conclusion proof) claim);
  assert (Seq.for_all (fun premise -> List.exists (equal_formula premise) allowed_axioms) (judgement_premises proof));
  print_endline ("Verified: " ^ string_of_formula claim)

let main () =
  print_endline "Set theory axioms:";
  print_endline ("  Extensionality   " ^ string_of_formula Axioms.extensionality);
  print_endline ("  Substitution     " ^ string_of_formula Axioms.substitution);
  print_endline ("  Pair             " ^ string_of_formula Axioms.pair);
  print_endline ("  Union            " ^ string_of_formula Axioms.union);
  print_endline ("  Regularity       " ^ string_of_formula Axioms.regularity);
  print_endline ("  Replacement      " ^ string_of_formula Axioms.replacement);
  (* print_endline ("  Tarski           " ^ string_of_formula Axioms.tarski); *)

  print_newline ();
  print_endline (string_of_predicate Singleton.pred);
  verify Singleton.exists_proof (Fun1.existence Singleton.pred);
  verify Singleton.unique_proof (Fun1.uniqueness Singleton.pred);
