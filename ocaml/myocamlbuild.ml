open Ocamlbuild_plugin;;
open Command;;

dispatch begin function
  | Before_rules ->
    begin
    end
  | After_rules ->
    begin
      flag ["ocaml";"compile";"dparsetree"] (S [A "-dparsetree"]);
      flag ["ocaml";"compile";"dtypedtree"] (S [A "-dtypedtree"]);
      flag ["ocaml";"compile";"drawlambda"] (S [A "-drawlambda"]);
      flag ["ocaml";"compile";"dlambda"] (S [A "-dlambda"]);
      flag ["ocaml";"compile";"native";"dflambda"] (S [A "-dflambda"]);
      flag ["ocaml";"compile";"native";"drawflambda"] (S [A "-drawflambda"]);
      flag ["ocaml";"compile";"native";"dflambda-no-invariants"] (S [A "-dflambda-no-invariants"]);
      flag ["ocaml";"compile";"native";"dflambda-verbose"] (S [A "-dflambda-verbose"]);
    end
  | _ -> ()
end
