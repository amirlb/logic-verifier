module Proposition = Logic.Kernel.Proposition
module Kernel = Logic.Kernel.String

module U = struct
  let meta s = Proposition.mk_meta s
  let atom s = Proposition.mk_fun s []
  let func s args = Proposition.mk_fun s args

  let pp_term fmt t = Format.pp_print_string fmt (Proposition.to_string
                                                    (fun x -> x)
                                                    t)

  let equal_term t t' = 0 = Proposition.compare String.compare t t'

  let pp_unification_error fmt (e : Kernel.unification_error) = match e with
    | Occurs(v, t) -> Format.fprintf fmt "Occurs(%s, " v;
                      pp_term fmt t;
                      Format.fprintf fmt ")"
    | Conflict(l, r) -> Format.fprintf fmt "Conflict(";
                        pp_term fmt l;
                        Format.fprintf fmt ", ";
                        pp_term fmt r;
                        Format.fprintf fmt ")"

  let equal_unification_error e e' = match e, e' with
    | Kernel.Occurs(v, t), Kernel.Occurs(v', t') -> String.equal v v' && equal_term t t'
    | Kernel.Conflict(l, r), Kernel.Conflict(l', r') -> equal_term l l' && equal_term r r'
    | _, _ -> false

  let unify l r = Kernel.unify l r
end

let uresult = Alcotest.(result
                          (list (pair string (testable U.pp_term U.equal_term)))
                          (testable U.pp_unification_error U.equal_unification_error))

let test_unify name l r res =
  Alcotest.test_case ("Unify." ^ name) `Quick (fun () ->
      Alcotest.(check uresult) name res (U.unify l r)
    )

let () =
  let open Alcotest in
  let a = U.atom "a"
  and b = U.atom "b"
  and x = U.meta "X"
  and y = U.meta "Y"
  in
  let fX = U.func "f" [x]
  and gX = U.func "g" [x]
  and fY = U.func "f" [y]
  and gY = U.func "g" [y]
  in
  run "Kernel" [
      "unify",  [
        test_unify "aa" a a (Ok []);
        test_unify "ab" a b (Error (Conflict(a, b)));
        test_unify "XX" x x (Ok []);
        test_unify "aX" a  x (Ok [("X", a)]);
        test_unify "faX_faB" (U.func "f" [a; x]) (U.func "f" [a; b]) (Ok [("X", b)]);
        test_unify "fa_ga" (U.func "f" [a]) (U.func "g" [a]) (Error U.(Conflict(func "f" [a], func "g" [a])));
        test_unify "fX_fY" fX fY (Ok ["Y", x]);
        test_unify "fX_gY" fX gY (Error(Conflict(fX, gY)));
        test_unify "fX_fXZ" fX (U.func "f" [x; U.meta "Z"]) (Error U.(Conflict(fX , func "f" [x; U.meta "Z"])));
        test_unify "fgX_fY" U.(func "f" [gX]) fY (Ok ["Y", gX]);

        test_unify "X_fX" x fX (Error (Occurs("X", fX)));

        test_unify "fgXX_fYa" U.(func "f" [gX; x]) (U.func "f" [y; a]) (Ok ["X", a; "Y", U.func "g" [a]]);
      ]
    ]
