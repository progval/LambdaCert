module StringSet = Set.Make(String)

let rec string_of_value_loc depth st loc =
  if (depth = 0) then
    "<cut>"
  else
    match (Store.get_value st loc) with
      | None -> "<reference to non-existing value>"
      | Some v -> string_of_value (depth-1) st v
and string_of_value depth st = function
| Values.Null -> "null"
| Values.Undefined -> "undefined"
| Values.Number f -> CoqUtils.implode (JsNumber.to_string f)
| Values.String s -> "\"" ^ (CoqUtils.implode s) ^ "\""
| Values.True -> "true"
| Values.False -> "false"
| Values.Object ptr -> string_of_object_ptr depth st ptr
| Values.Closure (_, loc_heap, args, body) ->
    Printf.sprintf "<closure func (%s) { %s }>"
      (String.concat ", " (List.map CoqUtils.implode args))
      (string_of_expression depth body)
and string_of_value_loc_option depth st = function
| Some v -> string_of_value_loc depth st v
| None -> "<unset val>"

and string_of_object_ptr depth st ptr =
  match (Store.get_object st ptr) with
    | None -> "<reference to non-existing object>"
    | Some obj -> string_of_object depth st obj
and string_of_object depth st obj =
  Printf.sprintf "{[#proto: %s, #class: %s, #extensible: %B, #primval: %s, #code: %s] %s}"
  (string_of_value_loc depth st obj.Values.object_proto) (CoqUtils.implode obj.Values.object_class)
  (obj.Values.object_extensible) (string_of_value_loc_option depth st obj.Values.object_prim_value)
  (string_of_value_loc_option depth st obj.Values.object_code)
  (string_of_prop_list depth st (Values.Heap.to_list obj.Values.object_properties_))
and string_of_prop_list depth st l =
  let string_of_prop = function (name, attr) ->
    Printf.sprintf "'%s': %s" (CoqUtils.implode name) (string_of_attr depth st attr)
  in let rec string_of_prop_list_aux props skip acc =
    match props with
    | [] -> acc
    | (name, value) :: tl ->
        if StringSet.mem (CoqUtils.implode name) skip then
          string_of_prop_list_aux tl skip acc
        else
          string_of_prop_list_aux tl (StringSet.add (CoqUtils.implode name) skip) (acc ^ ", " ^ (string_of_prop (name, value)))
  in match l with
  | [] -> ""
  | (name, value) :: tl -> string_of_prop_list_aux tl (StringSet.singleton (CoqUtils.implode name)) (string_of_prop (name, value))

and string_of_expression depth e =
  "<expr>"
and string_of_expression_option depth = function
| Some e -> string_of_expression depth e
| None -> "<unset expr>"

and string_of_attr depth st = function
| Values.Coq_attributes_data_of d -> Values.attributes_data_rect (fun v w c e -> Printf.sprintf "{#value %s, #writable %B, #configurable %B, #enumerable %B}" (string_of_value_loc depth st v) w c e) d
| Values.Coq_attributes_accessor_of d -> Values.attributes_accessor_rect (fun g s e c -> Printf.sprintf "{#getter %s, #setter %s}" (string_of_value_loc depth st g) (string_of_value_loc depth st s)) d (* enumerable and configurable ignored *)

let string_of_store depth st =
  let locs = (Utils.Heap.to_list st.Store.loc_heap) in
  let pred = string_of_value_loc depth st in
  String.concat "" (List.map (fun (k, v) -> Printf.sprintf "let (%s = %s) \n" (CoqUtils.implode k) (pred v)) locs)
