open Logic.Verifier

module Axioms = struct
  let member = make_builtin ~arity:2 ~name:"member"
  let member x y = apply member [x; y]
  let equal = make_builtin ~arity:2 ~name:"equal"
  let equal x y = apply equal [x; y]

  let subset = predicate_of_formula ~arity:2 ~name:"subset" (function [a; b] ->
    forall ~name:"x" (fun x -> (implies (member x a) (member x b))) | _ -> failwith "")

  let substitution =
    forall ~name:"x" (fun x -> forall ~name:"y" (fun y ->
      forall2 ~arity:1 ~name:"p" (fun p -> implies (equal x y) (iff (apply p [x]) (apply p [y])))))
  let extensionality =
    forall ~name:"a" (fun a -> forall ~name:"b" (fun b ->
      implies (forall ~name:"x" (fun x -> iff (member x a) (member x b))) (equal a b)))
  let regularity =
    forall ~name:"a" (fun a -> implies (exists ~name:"x" (fun x -> member x a)) (exists ~name:"y" (fun y -> and_ (member y a) (not_ (exists ~name:"z" (fun z -> and_ (member z a) (member z y)))))))

  let pair =
    forall ~name:"x" (fun x -> forall ~name:"y" (fun y ->
      exists ~name:"z" (fun z -> forall ~name:"a" (fun a -> iff (member a z) (or_ (equal a x) (equal a y))))))
  let union =
    forall ~name:"a" (fun a -> exists ~name:"z" (fun z -> forall ~name:"x" (fun x -> iff (member x z) (exists ~name:"y" (fun y -> and_ (member x y) (member y a))))))
  let power =
    forall ~name:"a" (fun a -> exists ~name:"z" (fun z -> forall ~name:"x" (fun x -> iff (member x z) (apply subset [x; a]))))
  let replacement =
    forall ~name:"a" (fun a -> forall2 ~arity:2 ~name:"P" (fun p -> implies (forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> forall ~name:"z" (fun z -> implies (and_ (apply p [x; y]) (apply p [x; z])) (equal y z)))))
      (exists ~name:"b" (fun b -> forall ~name:"x" (fun x -> iff (member x b) (exists ~name:"y" (fun y -> and_ (member y a) (apply p [x; y]))))))))
  let infinity =
    exists ~name:"a" (fun a -> (and_
      (exists ~name:"x" (fun x -> member x a))
      (forall ~name:"x" (fun x -> implies (member x a) (exists ~name:"y" (fun y -> and_ (member x y) (member y a)))))))
  (* let choice =
    forall2 ~arity:2 ~name:"P" (fun p -> exists ~name:"r" (fun r ->
      forall ~name:"x" (fun x ->
        (implies (exists ~name:"y" (fun y -> apply p [x; y]))
                 (exists ~name:"y" (fun y -> (forall ~name:"z" (fun z -> iff (equal y z) (apply r [x; z]))))))))) *)

  let zfc = [
    substitution;
    extensionality;
    regularity;
    pair;
    union;
    power;
    replacement;
    infinity;
    (* choice; *)
  ]
end

module Fun0 = struct
  let existence pred =
    exists ~name:"a" (fun a -> apply pred [a])

  let uniqueness pred =
    forall ~name:"a" (fun a -> forall ~name:"b" (fun b -> implies (and_ (apply pred [a]) (apply pred [b])) (Axioms.equal a b)))
end

module Fun1 = struct
  let existence pred =
    forall ~name:"x" (fun x -> exists ~name:"a" (fun a -> apply pred [x; a]))

  let uniqueness pred =
    forall ~name:"x" (fun x -> forall ~name:"a" (fun a -> forall ~name:"b" (fun b ->
      implies (and_ (apply pred [x; a]) (apply pred [x; b])) (Axioms.equal a b))))
end

module Fun2 = struct
  let existence pred =
    forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> exists ~name:"a" (fun a -> apply pred [x; y; a])))

  let uniqueness pred =
    forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> forall ~name:"a" (fun a -> forall ~name:"b" (fun b ->
      implies (and_ (apply pred [x; y; a]) (apply pred [x; y; b])) (Axioms.equal a b)))))
end

module EmptySet = struct
  let pred = predicate_of_formula ~arity:1 ~name:"empty_set" (function [a] -> forall ~name:"x" (fun x -> not_ (Axioms.member x a)) | _ -> failwith "")

  let existence =
    let m_p = consequence [pattern_implies (metavar 1) (metavar 2); metavar 1] (metavar 2) in
    let some_prop = forall ~name:"x" (fun x -> Axioms.equal x x) in
    let falsehood = and_ some_prop (not_ some_prop) in
    let infinity_implies_empty = inst_exists Axioms.infinity (fun some_set _ ->
      let p = predicate_of_formula ~arity:2 ~name:"p" (fun _ -> falsehood) in
      let p_func = intro_forall ~name:"x" (fun x -> intro_forall ~name:"y" (fun y -> intro_forall ~name:"z" (fun z ->
        infer
          (consequence [] (pattern_implies (pattern_and (pattern_and (metavar 1) (pattern_not (metavar 1))) (pattern_and (metavar 2) (pattern_not (metavar 2)))) (metavar 3)))
          [] (implies (and_ (apply p [x; y]) (apply p [x; z])) (Axioms.equal y z))))) in
      let ex_replaced = infer m_p [elim_forall2 p (elim_forall some_set (assertion Axioms.replacement)); p_func]
        (exists ~name:"b" (fun b -> forall ~name:"x" (fun x -> iff (Axioms.member x b) (exists ~name:"y" (fun y -> and_ (Axioms.member y some_set) (apply p [x; y])))))) in
      let ex_replaced_implies_empty = inst_exists (judgement_conclusion ex_replaced) (fun the_set replacement ->
        intro_exists the_set
          (intro_forall ~name:"x" (fun x ->
            let prop_implies_falsehood = inst_exists
              (exists ~name:"y" (fun y -> and_ (Axioms.member y some_set) (apply p [x; y])))
              (fun _ prop -> infer (consequence [pattern_and (metavar 1) (metavar 2)] (metavar 2)) [prop] falsehood) in
            infer
              (consequence [pattern_iff (metavar 1) (metavar 2); pattern_implies (metavar 2) (pattern_and (metavar 3) (pattern_not (metavar 3)))] (pattern_not (metavar 1)))
              [elim_forall x replacement; prop_implies_falsehood]
              (not_ (Axioms.member x the_set))))) in
      infer m_p [ex_replaced_implies_empty; ex_replaced] (exists ~name:"a" (fun a -> apply pred [a]))
    ) in
    infer m_p [infinity_implies_empty; assertion Axioms.infinity] (Fun0.existence pred)

  let uniqueness =
    intro_forall ~name:"a" (fun a -> intro_forall ~name:"b" (fun b ->
      assuming (and_ (apply pred [a]) (apply pred [b])) (fun assumptions ->
        let a_empty = infer (consequence [pattern_and (metavar 1) (metavar 2)] (metavar 1)) [assumptions] (apply pred [a]) in
        let b_empty = infer (consequence [pattern_and (metavar 1) (metavar 2)] (metavar 2)) [assumptions] (apply pred [b]) in
        let m_p = consequence [pattern_implies (metavar 1) (metavar 2); metavar 1] (metavar 2) in
        let ext = elim_forall b (elim_forall a (assertion Axioms.extensionality)) in
        let same_members = intro_forall ~name:"x" (fun x ->
          infer (consequence [pattern_not (metavar 1); pattern_not (metavar 2)] (pattern_iff (metavar 1) (metavar 2)))
            [elim_forall x a_empty; elim_forall x b_empty]
            (iff (Axioms.member x a) (Axioms.member x b))) in
        infer m_p [ext; same_members] (Axioms.equal a b))))
end

module Singleton = struct
  let pred = predicate_of_formula ~arity:2 ~name:"singleton" (function [x; a] -> forall ~name:"z" (fun z -> iff (Axioms.member z a) (Axioms.equal z x)) | _ -> failwith "")

  let existence = (let pair = assertion Axioms.pair in
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

  let uniqueness = (let ext = assertion Axioms.extensionality in
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

module Equality = struct
  let reflexivity =
    intro_forall ~name:"x" (fun x ->
      let iff_self = consequence [] (pattern_iff (metavar 1) (metavar 1)) in
      let m_p = consequence [pattern_implies (metavar 1) (metavar 2); metavar 1] (metavar 2) in
      let ext = elim_forall x (elim_forall x (assertion Axioms.extensionality)) in
      let same_members = intro_forall ~name:"z" (fun z ->
        infer iff_self [] (iff (Axioms.member z x) (Axioms.member z x))) in
      infer m_p [ext; same_members] (Axioms.equal x x))

  let symmetry =
    intro_forall ~name:"x" (fun x -> intro_forall ~name:"y" (fun y ->
      assuming (Axioms.equal x y) (fun x_eq_y ->
        let p = elim_forall2 (predicate_of_formula ~arity:1 ~name:"eq_x" (function [a] -> Axioms.equal a x | _ -> failwith ""))
          (elim_forall y (elim_forall x (assertion Axioms.substitution))) in
        infer
          (consequence [metavar 1; metavar 2; pattern_implies (metavar 1) (pattern_iff (metavar 2) (metavar 3))] (metavar 3))
          [x_eq_y; elim_forall x reflexivity; p] (Axioms.equal y x))))

  let transitivity =
    intro_forall ~name:"x" (fun x -> intro_forall ~name:"y" (fun y -> intro_forall ~name:"z" (fun z ->
      assuming (and_ (Axioms.equal x y) (Axioms.equal y z)) (fun assumptions ->
        let p = elim_forall2 (predicate_of_formula ~arity:1 ~name:"eq_z" (function [a] -> Axioms.equal a z | _ -> failwith ""))
          (elim_forall y (elim_forall x (assertion Axioms.substitution))) in
        infer
          (consequence [pattern_and (metavar 1) (metavar 2); pattern_implies (metavar 1) (pattern_iff (metavar 3) (metavar 2))] (metavar 3))
          [assumptions; p] (Axioms.equal x z)))))
end

let verify proof claim =
  assert (equal_formula (judgement_conclusion proof) claim);
  assert (Seq.for_all (fun premise -> List.exists (equal_formula premise) Axioms.zfc) (judgement_premises proof));
  print_endline ("Verified: " ^ string_of_formula claim)

let verify_conclusion proof =
  verify proof (judgement_conclusion proof)

let main () =
  print_endline "Set theory axioms:";
  print_endline ("  Substitution     " ^ string_of_formula Axioms.substitution);
  print_endline ("  Extensionality   " ^ string_of_formula Axioms.extensionality);
  print_endline ("  Regularity       " ^ string_of_formula Axioms.regularity);
  print_endline ("  Pair             " ^ string_of_formula Axioms.pair);
  print_endline ("  Union            " ^ string_of_formula Axioms.union);
  print_endline ("  Power set        " ^ string_of_formula Axioms.power);
  print_endline ("  Replacement      " ^ string_of_formula Axioms.replacement);
  print_endline ("  Infinity         " ^ string_of_formula Axioms.infinity);
  (* print_endline ("  Choice           " ^ string_of_formula Axioms.choice); *)

  print_newline ();
  verify_conclusion Equality.reflexivity;
  verify_conclusion Equality.symmetry;
  verify_conclusion Equality.transitivity;

  print_newline ();
  print_endline (string_of_predicate EmptySet.pred);
  verify EmptySet.existence (Fun0.existence EmptySet.pred);
  verify EmptySet.uniqueness (Fun0.uniqueness EmptySet.pred);

  print_newline ();
  print_endline (string_of_predicate Singleton.pred);
  verify Singleton.existence (Fun1.existence Singleton.pred);
  verify Singleton.uniqueness (Fun1.uniqueness Singleton.pred);
