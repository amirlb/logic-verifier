module P = Logic.Verifier.Pattern
module F = Logic.Verifier.Formula
module V = Logic.Verifier.Verifier

let example_1 =
  let equal = Logic.Verifier.make_builtin 2 "equal" in
  let self_equal x = F.apply equal [x; x] in
  let gen_p_imp_p = F.(forall (fun x -> implies (self_equal x) (self_equal x))) in
  let proof = V.(intro_forall (fun x -> (assuming (self_equal x) (fun p -> p)))) in
  (gen_p_imp_p, proof)

let example_2 =
  let member = Logic.Verifier.make_builtin 2 "member" in
  let subset a b = F.(forall (fun x -> implies (apply member [x; a]) (apply member [x; b]))) in
  let a_ss_b_ss_c a b c = F.(and_ (subset a b) (subset b c)) in
  let claim = F.(forall (fun a -> forall (fun b -> forall (fun c -> implies (a_ss_b_ss_c a b c) (subset a c))))) in

  let conj_1 = P.(consequence [and_ (metavar 1) (metavar 2)] (metavar 1)) in
  let conj_2 = P.(consequence [and_ (metavar 1) (metavar 2)] (metavar 2)) in
  let m_p = P.(consequence [implies (metavar 1) (metavar 2); metavar 1] (metavar 2)) in
  let proof = V.(intro_forall (fun a -> intro_forall (fun b -> intro_forall (fun c -> assuming (a_ss_b_ss_c a b c) (fun p ->
    let a_ss_b = infer conj_1 [p] (subset a b) in
    let b_ss_c = infer conj_2 [p] (subset b c) in
    intro_forall (fun x ->
      assuming F.(apply member [x; a]) (fun x_in_a -> 
        let x_in_b = infer m_p [elim_forall x a_ss_b; x_in_a] F.(apply member [x; b]) in
        let x_in_c = infer m_p [elim_forall x b_ss_c; x_in_b] F.(apply member [x; c]) in
        x_in_c
      ))))))) in

  (claim, proof)

let example_3 =
  let member = Logic.Verifier.make_builtin 2 "member" in
  let tautology x y = F.(or_ (apply member [x; y]) (not_ (apply member [x; y]))) in
  let claim = F.(forall (fun x -> forall (fun y -> tautology x y))) in

  let p_or_not_p = P.(consequence [] (or_ (metavar 0) (not_ (metavar 0)))) in
  let proof = V.(intro_forall (fun x -> intro_forall (fun y -> infer p_or_not_p [] (tautology x y)))) in

  (claim, proof)

let example_4 =
  let equal = Logic.Verifier.make_builtin 2 "equal" in
  let member = Logic.Verifier.make_builtin 2 "member" in
  let axiom = F.(forall2 1 (fun p -> forall (fun x -> forall (fun y ->
    implies (apply equal [x; y]) (iff (apply p [x]) (apply p [y])))))) in
  let not_empty a = F.(exists (fun x -> apply member [x; a])) in
  let claim = F.(implies axiom (forall (fun a -> forall (fun b ->
    implies (and_ (not_empty a) (apply equal [a; b])) (not_empty b))))) in

  let conj_1 = P.(consequence [and_ (metavar 1) (metavar 2)] (metavar 1)) in
  let conj_2 = P.(consequence [and_ (metavar 1) (metavar 2)] (metavar 2)) in
  let m_p = P.(consequence [implies (metavar 1) (metavar 2); metavar 1] (metavar 2)) in
  let m_p_iff = P.(consequence [iff (metavar 1) (metavar 2); metavar 1] (metavar 2)) in
  let proof = V.(assuming axiom (fun axiom ->
    intro_forall (fun a -> intro_forall (fun b ->
      assuming (F.(and_ (not_empty a) (apply equal [a; b]))) (fun p ->
        let a_not_empty = infer conj_1 [p] (not_empty a) in
        let a_eq_b = infer conj_2 [p] (F.(apply equal [a; b])) in
        let not_empty_pred = Logic.Verifier.Predicate.from_formula 1
          (function [a] -> not_empty a | _ -> failwith "") in
        let not_empty_eq = elim_forall2 not_empty_pred axiom in
        let iff = infer m_p
          [elim_forall b (elim_forall a not_empty_eq); a_eq_b]
          F.(iff (not_empty a) (not_empty b)) in
        infer m_p_iff [iff; a_not_empty] (not_empty b)
  ))))) in

  (claim, proof)

let example_5 =
  let comprehension p_1 =
    F.(not_ (forall2 1 (fun phi -> not_ (forall (fun x -> iff (p_1 x) (apply phi [x])))))) in

  let prove_comprehension p_1 = V.(
    let a_iff_a = P.(consequence [] (iff (metavar 1) (metavar 1))) in
    let conj = P.(consequence [metavar 1; metavar 2] (and_ (metavar 1) (metavar 2))) in
    let by_contradiction = P.(consequence [implies (metavar 1) (and_ (metavar 2) (not_ (metavar 2)))] (not_ (metavar 1))) in

    let tautology x = F.(iff (p_1 x) (p_1 x)) in
    let gen_tautology = F.(forall tautology) in

    let not_comp = F.(forall2 1 (fun p -> not_ (forall (fun x -> iff (p_1 x) (apply p [x]))))) in
    infer by_contradiction
      [assuming not_comp (fun not_comp ->
        (infer conj
          [
            intro_forall (fun x -> infer a_iff_a [] (tautology x));
            elim_forall2
              (Logic.Verifier.Predicate.from_formula 1 (function [x] -> p_1 x | _ -> failwith ""))
              not_comp
          ]
          F.(and_ gen_tautology (not_ gen_tautology)))
      )]
      (comprehension p_1)
  ) in

  let member = Logic.Verifier.make_builtin 2 "member" in
  let not_empty a = F.(exists (fun x -> apply member [x; a])) in
  (comprehension not_empty, prove_comprehension not_empty)

let validate (claim, proof) =
  assert (Seq.is_empty (V.premises proof));
  assert (V.conclusion proof = claim);
  Printf.printf "Verified: %s\n" (F.to_string claim)

let main () =
  validate example_1;
  validate example_2;
  validate example_3;
  validate example_4;
  validate example_5;
