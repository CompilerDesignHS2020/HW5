open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with
  (* Axioms *)
  | TInt, TInt -> true

  | TBool, TBool -> true

  | TNullRef(i1), TNullRef(i2) -> subtype_ref c i1  i2
  | TRef(i1), TRef(i2) -> subtype_ref c i1  i2
  | TRef(i1), TNullRef(i2) -> subtype_ref c i1  i2

  | _ ,_ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1, t2 with
  (* Axioms *)
  | RString, RString -> true
  | RArray(i1), RArray(i2) -> i1 = i2
  | RStruct(i1), RStruct(i2) -> subtype_struct c i1 i2
  | RFun(args1, rt1), RFun(args2, rt2) -> (subtype_funarg c args2 args1) && subtype_ret c rt1 rt2
  | _ ,_ -> false

and subtype_ret (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
  match t1, t2 with
  | RetVoid, RetVoid -> true
  | RetVoid, _ -> false
  | _ , RetVoid -> false
  | RetVal(i1), RetVal(i2) -> subtype c i1 i2


and subtype_struct (c : Tctxt.t) (t1 : Ast.id) (t2 : Ast.id) : bool =
  
  let larger_struct_fields = lookup_struct t1 c in
  let smaller_struct_fields = lookup_struct t2 c in

  let rec check_fields rem_larger_fields rem_smaller_fields = 
    match rem_smaller_fields with
    | [] -> true
    | h_smaller::tl_smaller-> 
      begin match rem_larger_fields with
      | [] -> false
      | h_larger::tl_larger -> 
        if h_larger = h_smaller then
          check_fields tl_larger tl_smaller
        else
          false
      end
  in

  check_fields larger_struct_fields smaller_struct_fields

and subtype_funarg (c : Tctxt.t) (args1 : Ast.ty list) (args2 : Ast.ty list) : bool =

  let rec check_rem_args rem_args_1 rem_args_2 =
    match rem_args_1 with
    | [] -> true
    | h1::tl1 -> 
      begin match rem_args_2 with
      | h2::tl2 ->
        if subtype c h1 h2 then
          check_rem_args tl1 tl2
        else
          false
      | [] -> false
      end
  in

  if List.length args1 = List.length args2 then
    check_rem_args args1 args2
  else
    false


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is 

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TBool -> ()
  | TInt -> ()
  | TRef(i) -> typecheck_rty l tc i
  | TNullRef(i) -> typecheck_rty l tc i

and typecheck_rty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  match t with
  | RString -> ()
  | RArray(i) -> typecheck_ty l tc i
  | RStruct(i) ->
      begin match lookup_struct_option i tc with
        | None -> type_error l ("Struct "^i^" not defined")
        | Some field_list -> ()
      end
  | RFun(args, rty) -> typecheck_fun_args l tc args ;typecheck_retty l tc rty

and typecheck_retty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit =
  match t with
  | RetVoid -> ()
  | RetVal(i) -> typecheck_ty l tc i

and typecheck_fun_args (l : 'a Ast.node) (tc : Tctxt.t) (args : Ast.ty list) : unit =
  let rec check_rem_args rem_args =
    match rem_args with
    | [] -> ()
    | h::tl -> typecheck_ty l tc h; check_rem_args tl
  in

  check_rem_args args


(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)


let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
    | CNull(cons) -> typecheck_rty e c cons; TNullRef cons
    | CBool(b) -> TBool
    | CInt(i) -> TInt
    | CStr(s) -> TRef RString
    | Id(id) -> begin match lookup_option id c with
      | Some(t) -> t
      | None -> 
        begin match lookup_global_option id c  with
          | Some(t) -> t
          | None -> type_error e ("variable not defined: "^id)
        end
      end
    | CArr(arr_ty, init_exp_list) -> 
      typecheck_ty e c arr_ty; (* check if array's inner type is valid *)
      are_subs_of c init_exp_list arr_ty; (* check if type of init expressions matches array's inner type *)
      TRef(RArray(arr_ty)) (* return array type *)

    | NewArr(arr_ty, size_exp, id, init_exp) -> 
      typecheck_ty e c arr_ty; (* check if array's inner type is valid *)
      if subtype c (typecheck_exp c size_exp) TInt then (* Check if size expression is of type int *)
        ()
      else
        type_error e ("Array size is not of type int")
      ; 
      begin match lookup_option id c with (* check if id is not yet in local scope *)
        | None -> ()
        | Some(t) -> type_error e (id^"already definded in local scope")
      end
      ;
      if subtype c (typecheck_exp (add_local c id TInt) init_exp) arr_ty then (* check if init_exp is subtype of inner type *)
        ()
      else
        type_error e ("Initialize expression does not match the array type")
      ; 
      TRef(RArray(arr_ty)) (* return array type *)

    | Index(array_exp, index_exp) ->
      let type_of_arr_exp = typecheck_exp c array_exp in (* Check if array expression is of type array *)
      let outer_type, inner_type =
        begin match type_of_arr_exp with
          | TRef(RArray(i)) -> TRef(RArray(i)), i
          | _ -> type_error e ("Indexing non array type")
        end
      in ();
      if subtype c (typecheck_exp c index_exp) TInt then (* Check if size expression is of type int *)
        ()
      else
        type_error e ("Array index is not of type int")
      ;
      inner_type (* return array type *)
    
    | Length(arr_exp) ->
      let type_of_arr_exp = typecheck_exp c arr_exp in (* Check if array expression is of type array *)
      begin match type_of_arr_exp with
        | TRef(RArray(i)) -> ()
        | _ -> type_error e ("Applying lenght to non array type")
      end
      ;
      TInt;  (* return int type *)

    | CStruct(struct_id, field_init_exp_list) -> 
      (* check if struct is defined *)
      begin match lookup_struct_option struct_id c with
        | None -> type_error e ("struct "^struct_id^" is not defined")
        | Some t -> ()
      end
      ;
      (* check if they field init types expresstions match *)
      check_field_types c struct_id field_init_exp_list;
      TRef(RStruct(struct_id)); (* return struct type *)

    | Proj(struct_exp, field_id) -> 
      (* check if struct_exp is a struct *)
      let struct_name = 
        match typecheck_exp c struct_exp with
        | TRef(RStruct(id)) -> id
        | _ -> type_error e "trying to access field of non struct object"
      in
      (* check if field exists in struct *)
      let field_type =
        begin match lookup_field_option struct_name field_id c with
          | None -> type_error struct_exp (field_id^" is not present in struct "^struct_name)
          | Some field_type -> field_type
        end
      in
      (* return field type *)
      field_type

    
    | Call(fun_exp, arg_exp_list) ->
      (* check fun_exp *)
      let function_type = typecheck_exp c fun_exp in

      let arg_ty_list, ret_ty = 
        match function_type with
        | TRef(RFun(arg_tys, rty)) -> arg_tys, rty
        | _ -> type_error e "no function type"
      in

      (* check args *)
      are_subs_of_list c arg_exp_list arg_ty_list fun_exp;
      
      (* return retrun type *)
      let effective_ret_type = 
        match ret_ty with
        | RetVal(t) -> t
        | RetVoid -> type_error e "expression must not return void"
      in
      effective_ret_type

    | Bop(binop_type, exp1, exp2) -> 

      begin match binop_type with
      | Eq | Neq -> 
        (* get types of expressions *)
        let ty1 = typecheck_exp c exp1 in
        let ty2 = typecheck_exp c exp2 in

        if subtype c ty1 ty2 && subtype c ty2 ty1 then
          ()
        else
          type_error e "types of == and != must match"
        ;
        TBool

      | _ ->

        (* get types of binop  *)
        let (t1, t2, res_t) = typ_of_binop binop_type in

        (* check if type of exps are correct *)
        if subtype c (typecheck_exp c exp1) t1 then
          ()
        else
          type_error e "first expression of binop does not match type of binop"
        ;

        if subtype c (typecheck_exp c exp2) t2 then
          ()
        else
          type_error e "first expression of binop does not match type of binop"
        ;

        (* return result type *)
        res_t

      end

    | Uop(uop_type, exp) -> 
      (* get types of uop  *)
      let (t1, res_t) = typ_of_unop uop_type in

      (* check if type of exp is correct *)
      if subtype c (typecheck_exp c exp) t1 then
        ()
      else
        type_error e "expression of uop does not match type of uop"
      ;

      (* return result type *)
      res_t

and are_subs_of_list (c : Tctxt.t) (e : Ast.exp node list) (t: Ast.ty list) fun_exp =
  let rec are_rem_subs_list rem_exps rem_types =
    match rem_exps with
    | [] -> ()
    | h::tl -> 
      begin match rem_types with
      | [] -> type_error h "number of function arguments not matching"
      | h_ty::tl_ty -> 
        if subtype c (typecheck_exp c h) h_ty then
          are_rem_subs_list tl tl_ty
        else
          type_error h "function arguments do not match"
      end
  in

  if List.length e != List.length t then type_error fun_exp "number of function arguments not matching";

  are_rem_subs_list e t

and are_subs_of (c : Tctxt.t) (e : Ast.exp node list) (t: Ast.ty) =
  let rec are_rem_subs rem_exps =
    match rem_exps with
    | [] -> ()
    | h::tl -> 
      if subtype c (typecheck_exp c h) t then
        are_rem_subs tl
      else
        type_error h "initialize expression does not match array type"
  in

  are_rem_subs e

and check_field_types (c : Tctxt.t) (struct_name: Ast.id) (struct_init_list: (Ast.id * Ast.exp Ast.node) list) : unit =

(*iterate over all struct elems, in a struct_elem list
if corresponding init_list elem found, "delete" elems from both lists *)
let rec check_struct_field rem_struct_fields rem_init_elems = 
  begin match rem_struct_fields with
    | [] ->  begin match rem_init_elems with
        | [] -> () (*succeded, both lists empty*)
        | (init_ty_h, init_node_h)::init_tl -> type_error init_node_h ("init_list has too much elems")
      end
    | (struct_field_h)::struct_field_tl -> 
      begin match rem_init_elems with
        | [] -> type_error (Ast.no_loc()) ("init_list has unsued elems")
        | (init_ty_h, init_node_h)::init_tl -> 
          if subtype c (typecheck_exp c init_node_h) struct_field_h.ftyp then 
            check_struct_field struct_field_tl init_tl 
          else 
            type_error init_node_h ("elem missing in init_list")
      end
  end
in

let compare_struct_fields (arg1:Ast.field) (arg2:Ast.field) =
  if arg1.fieldName = arg2.fieldName then
    0
  else if arg1.fieldName > arg2.fieldName then
    1
  else
    -1
in

let compare_init_list (id1, exp1) (id2, exp2) =
  if id1 = id2 then
    0
  else if id1 > id2 then
    1
  else
    -1
in

let sort_struct_elem_list = List.sort compare_struct_fields (lookup_struct struct_name c) 
in
let sort_init_list = List.sort compare_init_list struct_init_list in
check_struct_field sort_struct_elem_list sort_init_list

(* adds variable to loacl context if not perviously defined, returns new context *)
let add_local_decl cur_txt id node exp = 
  begin match lookup_local_option id cur_txt with 
    | Some(_) -> type_error node (id^" previously defined")
    | None -> let new_ty = typecheck_exp cur_txt exp in
      add_local cur_txt id new_ty
  end



let add_local_decls ctxt node decl_list =
  let rec add_rem_local_decls cur_ctxt rem_decls =
    match rem_decls with
      | [] -> cur_ctxt
      | h::tl -> 
    let id, exp = h in
    let new_ctxt = add_local_decl cur_ctxt id node exp in
    add_rem_local_decls new_ctxt tl
  in
  add_rem_local_decls ctxt decl_list



(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statment typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
(*if illegal stmt, typecheck_stmt fails*)

let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  begin match s.elt with
    | Assn(lhs, exp) -> 
      if subtype tc (typecheck_exp tc exp) (typecheck_exp tc lhs) then
        (tc, false)
      else
        type_error s ("ass: rhs not subtype of lhs")
    (* TODO: G⊢lhs lhs:t∈L or lhs not a global function id*)

    | Decl(id, exp) ->  
      (add_local_decl tc id s exp, false)  

    | SCall(fun_exp, arg_list) -> 
      (* check fun_exp *)
      let fun_ty = typecheck_exp tc fun_exp in

      let arg_ty_list, ret_ty = 
        match fun_ty with
        | TRef(RFun(arg_tys, rty)) -> arg_tys, rty
        | _ -> type_error s "no function type"
      in

      (* check args *)
      are_subs_of_list tc arg_list arg_ty_list fun_exp;
      
      (* return return type *)
      begin match ret_ty with
        | RetVal(_) -> type_error s "expression must not return void"
        | RetVoid -> (tc, false)
      end
    
    | If (if_exp, then_block, else_block) ->
      begin match typecheck_exp tc if_exp with
        | TBool -> 
          let (_, then_does_ret) = typecheck_block tc then_block to_ret in
          let (_, else_does_ret) = typecheck_block tc else_block to_ret in
          if (then_does_ret && else_does_ret) then
            (tc, true)
          else
            (tc, false)
        | _ -> type_error s ("if statement is not bool")
      end

    | While(exp, block) -> 
      if (typecheck_exp tc exp) = TBool then
        ()
      else
        type_error s ("condition in for statement is not of type bool")
      ;
      let _, _ = typecheck_block tc block to_ret in
      tc, false

    | For(vdecls, exp_opt, stmt_opt, block) ->
      (* add vdecls to local context *)
      let for_ctxt = add_local_decls tc s vdecls in
      begin match exp_opt with
        | Some(e) -> 
          if (typecheck_exp for_ctxt e) = TBool then
            ()
          else
            type_error s ("condition in for statement is not of type bool")
        | None -> ()
      end;
    
      begin match stmt_opt with
        | Some(e) -> 
          let _ = typecheck_stmt for_ctxt e to_ret in ()
        | None -> ()
      end;

      let _, _ =  typecheck_block for_ctxt block to_ret  in
      tc, false
      
    | Cast (ret_ty, id, if_null_exp, then_block, else_block) ->
      begin match typecheck_exp tc if_null_exp with
        | TNullRef(rty) -> 
          let new_ctxt = add_local tc id (TRef(rty)) in
          let (_, then_does_ret) = typecheck_block new_ctxt then_block to_ret in
            (tc, then_does_ret)
        | TRef(t) -> 
          let (_, else_does_ret) = typecheck_block tc else_block to_ret in
            (tc, else_does_ret)
        | _ -> type_error s ("ifq statement is not reference type")
      end
        
    
    | Ret(arg_option) ->
      begin match arg_option with
        | None -> 
          if to_ret = RetVoid then
            (tc, true)
          else
            type_error s ("function should return void")
        | Some(arg) -> 
          let act_ret_type = typecheck_exp tc arg in
          begin match to_ret with
            | RetVoid -> type_error s ("function returns value, but should return void")
            | RetVal(to_ret_ty) -> 
              if subtype tc act_ret_type to_ret_ty then
                (tc, true)
              else
                type_error s ("return type does not match")
          end
          
      end
  end


and typecheck_block act_ctxt act_stmt_nodes to_ret =
    begin match act_stmt_nodes with
      | [] -> (act_ctxt, false)
      | h::tl -> let (new_ctxt, does_ret) = typecheck_stmt act_ctxt h to_ret in
        if does_ret then 
          begin match tl with
            | [] -> (new_ctxt, true)
            | _ -> type_error (no_loc()) ("unreachable code after ret stmt")
          end
        else typecheck_block new_ctxt tl to_ret
    end

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  (* add args to local ctxt *)
  let rec add_args act_ctxt rem_args =
    begin match rem_args with
      | [] -> act_ctxt
      | (ty, id)::tl -> 
        let new_ctxt = add_local act_ctxt id ty in
        add_args new_ctxt tl
    end
  in
  let ctxt_args = add_args tc f.args in
  let (_, does_ret) = (typecheck_block ctxt_args f.body f.frtyp) in
  if does_ret then () else type_error l "fun does not return"
  
(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'S'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'F' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)


let create_struct_ctxt (p:Ast.prog) : Tctxt.t =

  let rec add_struct_decl struct_decl ctxt =
    let new_struct_id, new_field_list = struct_decl.elt in
    begin match lookup_struct_option new_struct_id ctxt with
      | None ->  add_struct ctxt new_struct_id new_field_list 
      | Some(id) -> type_error struct_decl ("struct "^new_struct_id^" declared twice")
    end
  in

  let rec process_rem_decls rem_decls cur_ctxt : Tctxt.t =
    match rem_decls with
    | [] -> cur_ctxt
    | Gvdecl(g)::tl -> process_rem_decls tl cur_ctxt
    | Gfdecl(f)::tl -> process_rem_decls tl cur_ctxt
    | Gtdecl(s)::tl -> process_rem_decls tl (add_struct_decl s cur_ctxt)
  in

  process_rem_decls p ({locals = []; globals = []; structs = []})

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =

  let rec extract_arg_types rem_args = 
    match rem_args with
    | [] -> []
    | (ty,id)::tl -> [ty]@(extract_arg_types tl)
  in

  let rec extract_builtin_arg_types rem_args = 
    match rem_args with
    | [] -> []
    | h::tl -> [h]@(extract_builtin_arg_types tl)
  in

  let rec process_rem_decls rem_decls cur_ctxt =
    match rem_decls with
    | [] -> cur_ctxt
    | Gvdecl(g)::tl -> process_rem_decls tl cur_ctxt
    | Gtdecl(s)::tl -> process_rem_decls tl cur_ctxt
    | Gfdecl(f)::tl -> 
    let id, fun_ty =   
      (f.elt.fname, TRef(RFun(extract_arg_types f.elt.args, f.elt.frtyp)))
    in
    let new_ctxt =
      match lookup_global_option id cur_ctxt  with
      | None -> add_global cur_ctxt id fun_ty
      | Some(t) -> type_error f ("function "^id^" declared twice")
    in
    process_rem_decls tl new_ctxt
  in

  let rec add_builtins (rem_builtins:(Ast.id * (Ast.ty list * Ast.ret_ty)) list) ctxt =
    match rem_builtins with
    | [] -> ctxt
    | (id, (arg_tys, ret_ty))::tl -> 
      let fun_ty = TRef(RFun(extract_builtin_arg_types arg_tys, ret_ty)) in
      let new_context = add_global ctxt id fun_ty in
      add_builtins tl new_context
  in

  let ctxt_with_builtins = add_builtins builtins tc in
  process_rem_decls p ctxt_with_builtins

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let rec process_rem_decls rem_decls cur_ctxt =
    match rem_decls with
    | [] -> cur_ctxt
    | Gfdecl(f)::tl -> process_rem_decls tl cur_ctxt
    | Gtdecl(s)::tl -> process_rem_decls tl cur_ctxt
    | Gvdecl(g)::tl -> 
      let id, ty = g.elt.name, (typecheck_exp tc g.elt.init) in
      let new_ctxt =
        match lookup_global_option id cur_ctxt  with
        | None -> add_global cur_ctxt id ty
        | Some(t) -> type_error g ("global variable "^id^" declared twice")
        
      in
      process_rem_decls tl new_ctxt
  in

  process_rem_decls p tc 


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
