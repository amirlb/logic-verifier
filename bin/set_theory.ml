open Logic.Verifier

module Axioms = struct
  let member = make_builtin ~arity:2 ~name:"member"
  let member x y = apply member [x; y]
  let equal = make_builtin ~arity:2 ~name:"equal"
  let equal x y = apply equal [x; y]

  let extensionality =
    forall ~name:"a" (fun a -> forall ~name:"b" (fun b -> implies (forall ~name:"x" (fun x -> iff (member x a) (member x b))) (equal a b)))
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

  let tarski =
    forall ~name:"n" (fun n -> exists ~name:"m" (fun m ->
      and_ (member n m)
      (and_ (forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> implies (and_ (member x m) (apply subset [y; x])) (member y m))))
      (forall ~name:"x" (fun x -> implies (member x m) (exists ~name:"z" (fun z -> (and_ (member z m) (forall ~name:"y" (fun y -> implies (apply subset [y; x]) (member y z)))))))))))
end

let main () =
  print_endline "Set theory axioms:";
  print_endline ("  Extensionality   " ^ string_of_formula Axioms.extensionality);
  print_endline ("  Pair             " ^ string_of_formula Axioms.pair);
  print_endline ("  Union            " ^ string_of_formula Axioms.union);
  print_endline ("  Regularity       " ^ string_of_formula Axioms.regularity);
  print_endline ("  Replacement      " ^ string_of_formula Axioms.replacement);
  print_endline ("  Tarski           " ^ string_of_formula Axioms.tarski);
