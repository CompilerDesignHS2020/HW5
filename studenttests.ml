open Assert

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests = [
  "subtype_stringQ_stringQ",
   (fun () ->
       if Typechecker.subtype Tctxt.empty (TNullRef RString) (TNullRef RString) then ()
       else failwith "should not fail")                                                                                     
; ("no_subtype_stringQ_stringQ",
   (fun () ->
       if Typechecker.subtype Tctxt.empty (TNullRef RString) (TRef RString) then
         failwith "should not succeed" else ())
  )
] 
