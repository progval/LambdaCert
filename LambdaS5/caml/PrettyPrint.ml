let string_of_object st v =
  "<object>"

let string_of_value st = function
| Values.Null -> "null"
| Values.Undefined -> "undefined"
| Values.Number f -> CoqUtils.implode (JsNumber.to_string f)
| Values.String s -> CoqUtils.implode s
| Values.True -> "true"
| Values.False -> "false"
| Values.ObjectLoc loc -> string_of_object st (Values.get_object_from_store st loc)

