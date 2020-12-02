open Assert
open Gradedtests

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.   *)

let subtype_tctxt: Tctxt.t = { locals = []; globals = []; structs = [
  ("Hobbit", [
      { fieldName = "name"; ftyp = TRef (RString) };
      { fieldName = "foot_size"; ftyp = TInt };
    ]);
  ("Frodo", [
      { fieldName = "name"; ftyp = TRef (RString) };
      { fieldName = "foot_size"; ftyp = TInt };
      { fieldName = "has_ring"; ftyp = TBool };
    ])
] }

let student_unit_tests = [
  "subtype_positive",
  (fun () ->
     if Typechecker.subtype Tctxt.empty (TRef (RStruct "Hobbit")) (TRef (RStruct "Frodo"))
     then ()
     else failwith "should not fail"
  );
  "subtype_negative",
  (fun () ->
     if not @@ Typechecker.subtype Tctxt.empty (TRef (RStruct "Hobbit")) (TRef (RStruct "Frodo"))
     then ()
     else failwith "should not fail"
  )
]

let oat_test = [
  ("oatprograms/joel_noah_sort_doner_shops.oat", "", "Nosh")
]

let provided_tests : suite = [
  GradedTest("custom_test", 5, executed_oat_file oat_test);
  GradedTest("subtype tests", 5, student_unit_tests);
]
