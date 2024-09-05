open Logic.Verifier

let example_1 =
  let equal = make_builtin ~arity:2 ~name:"equal" in
  let self_equal x = apply equal [x; x] in
  let gen_p_imp_p = forall ~name:"x" (fun x -> implies (self_equal x) (self_equal x)) in
  let proof = intro_forall ~name:"x" (fun x -> (assuming (self_equal x) (fun p -> p))) in
  (gen_p_imp_p, proof)

let example_2 =
  let member = make_builtin ~arity:2 ~name:"member" in
  let subset a b = forall ~name:"x" (fun x -> implies (apply member [x; a]) (apply member [x; b])) in
  let a_ss_b_ss_c a b c = and_ (subset a b) (subset b c) in
  let claim = forall ~name:"a" (fun a -> forall ~name:"b" (fun b -> forall ~name:"b" (fun c -> implies (a_ss_b_ss_c a b c) (subset a c)))) in

  let conj_1 = consequence [pattern_and (metavar 1) (metavar 2)] (metavar 1) in
  let conj_2 = consequence [pattern_and (metavar 1) (metavar 2)] (metavar 2) in
  let m_p = consequence [pattern_implies (metavar 1) (metavar 2); metavar 1] (metavar 2) in
  let proof = intro_forall ~name:"a" (fun a -> intro_forall ~name:"b" (fun b -> intro_forall ~name:"c" (fun c -> assuming (a_ss_b_ss_c a b c) (fun p ->
    let a_ss_b = infer conj_1 [p] (subset a b) in
    let b_ss_c = infer conj_2 [p] (subset b c) in
    intro_forall ~name:"x" (fun x ->
      assuming (apply member [x; a]) (fun x_in_a ->
        let x_in_b = infer m_p [elim_forall x a_ss_b; x_in_a] (apply member [x; b]) in
        let x_in_c = infer m_p [elim_forall x b_ss_c; x_in_b] (apply member [x; c]) in
        x_in_c
      )))))) in

  (claim, proof)

let example_3 =
  let member = make_builtin ~arity:2 ~name:"member" in
  let tautology x y = or_ (apply member [x; y]) (not_ (apply member [x; y])) in
  let claim = forall ~name:"x" (fun x -> forall ~name:"y" (fun y -> tautology x y)) in

  let p_or_not_p = consequence [] (pattern_or (metavar 0) (pattern_not (metavar 0))) in
  let proof = intro_forall ~name:"x" (fun x -> intro_forall ~name:"y" (fun y -> infer p_or_not_p [] (tautology x y))) in

  (claim, proof)

let example_4 =
  let equal = make_builtin ~arity:2 ~name:"equal" in
  let member = make_builtin ~arity:2 ~name:"member" in
  let axiom = forall2 ~arity:1 ~name:"p" (fun p -> forall ~name:"x" (fun x -> forall ~name:"y" (fun y ->
    implies (apply equal [x; y]) (iff (apply p [x]) (apply p [y]))))) in
  let not_empty a = exists ~name:"x" (fun x -> apply member [x; a]) in
  let claim = implies axiom (forall ~name:"a" (fun a -> forall ~name:"b" (fun b ->
    implies (and_ (not_empty a) (apply equal [a; b])) (not_empty b)))) in

  let conj_1 = consequence [pattern_and (metavar 1) (metavar 2)] (metavar 1) in
  let conj_2 = consequence [pattern_and (metavar 1) (metavar 2)] (metavar 2) in
  let m_p = consequence [pattern_implies (metavar 1) (metavar 2); metavar 1] (metavar 2) in
  let m_p_iff = consequence [pattern_iff (metavar 1) (metavar 2); metavar 1] (metavar 2) in
  let proof = assuming axiom (fun axiom ->
    intro_forall ~name:"a" (fun a -> intro_forall ~name:"b" (fun b ->
      assuming (and_ (not_empty a) (apply equal [a; b])) (fun p ->
        let a_not_empty = infer conj_1 [p] (not_empty a) in
        let a_eq_b = infer conj_2 [p] (apply equal [a; b]) in
        let not_empty_pred = predicate_of_formula ~arity:1
          (function [a] -> not_empty a | _ -> failwith "") in
        let not_empty_eq = elim_forall2 not_empty_pred axiom in
        let iff = infer m_p
          [elim_forall b (elim_forall a not_empty_eq); a_eq_b]
          (iff (not_empty a) (not_empty b)) in
        infer m_p_iff [iff; a_not_empty] (not_empty b)
  )))) in

  (claim, proof)

let example_5 =
  let comprehension p_1 =
    not_ (forall2 ~arity:1 ~name:"φ" (fun phi -> not_ (forall ~name:"x" (fun x -> iff (p_1 x) (apply phi [x]))))) in

  let prove_comprehension p_1 =
    let a_iff_a = consequence [] (pattern_iff (metavar 1) (metavar 1)) in
    let conj = consequence [metavar 1; metavar 2] (pattern_and (metavar 1) (metavar 2)) in
    let by_contradiction = consequence [pattern_implies (metavar 1) (pattern_and (metavar 2) (pattern_not (metavar 2)))] (pattern_not (metavar 1)) in

    let tautology x = iff (p_1 x) (p_1 x) in
    let gen_tautology = forall ~name:"x" tautology in

    let not_comp = forall2 ~arity:1 ~name:"p" (fun p -> not_ (forall ~name:"x" (fun x -> iff (p_1 x) (apply p [x])))) in
    infer by_contradiction
      [assuming not_comp (fun not_comp ->
        (infer conj
          [
            intro_forall ~name:"x" (fun x -> infer a_iff_a [] (tautology x));
            elim_forall2
              (predicate_of_formula ~arity:1 (function [x] -> p_1 x | _ -> failwith ""))
              not_comp
          ]
          (and_ gen_tautology (not_ gen_tautology)))
      )]
      (comprehension p_1)
  in

  let member = make_builtin ~arity:2 ~name:"member" in
  let not_empty a = exists ~name:"x" (fun x -> apply member [x; a]) in
  (comprehension not_empty, prove_comprehension not_empty)

let validate (claim, proof) =
  assert (Seq.is_empty (judgement_premises proof));
  assert (equal_formula (judgement_conclusion proof) claim);
  Printf.printf "Verified: %s\n" (string_of_formula claim)

let main () =
  validate example_1;
  validate example_2;
  validate example_3;
  validate example_4;
  validate example_5;
