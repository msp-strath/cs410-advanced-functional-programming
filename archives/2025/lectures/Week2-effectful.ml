
let rec zipWith f xs ys = match xs, ys with
  | x :: xs, y :: ys ->
     let z = f x y in
     let zs = zipWith f xs ys in
     z :: zs
  | _,_ -> []



let counting f =
  let counter = ref 0 in
  fun x y ->
    let v = !counter in
    let () = counter := v+1 in
    f x y + v

let zeros = zipWith (+)            [0; 0; 0] [0; 0; 0]
let nats  = zipWith (counting (+)) [0; 0; 0] [0; 0; 0]

let () = print_string "zeros"; print_newline()
let () = List.iter (fun i -> print_int i; print_newline()) zeros

let () = print_string "nats"; print_newline()
let () = List.iter (fun i -> print_int i; print_newline()) nats
