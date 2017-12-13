let lt = (List.append [1] []) in
(
(List.append [2] lt);
match lt with
       hd::tl -> match tl with hd2::tl2 -> print_int hd2
							|_ -> ()
		| _ -> ()
				 
				 );;