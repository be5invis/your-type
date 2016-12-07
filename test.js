const inference = require("./inference");
const type = require("./type");


const program = [
	["declare", "seq", ["forall", "'a", "'b", ["->", "'a", ["->", "'b", "'b"]]]],
	["declare", "car", ["forall", "'a", ["->", ["list", "'a"], "'a"]]],
	["declare", "cdr", ["forall", "'a", ["->", ["list", "'a"], ["list", "'a"]]]],
	["declare", "cons", ["forall", "'a", ["->", "'a", ["->", ["list", "'a"], ["list", "'a"]]]]],
	["declare", "newlist", ["forall", "'a", ["->", "unit", ["list", "'a"]]]],
	["declare", "empty?", ["forall", "'a", ["->", ["list", "'a"], "bool"]]],
	["declare", "0", "int"],
	["declare", "1", "int"],
	["declare", "true", "bool"],
	["declare", "false", "bool"],
	["declare", "nothing", "unit"],
	["declare", "+", ["forall", "'a",
		["->", "'a", ["->", "'a", "'a"]]]],
	["declare", "-", ["forall", "'a",
		["->", "'a", ["->", "'a", "'a"]]]],
	["declare", "==", ["forall", "'a",
		["->", "'a", ["->", "'a", "bool"]]]],
	["declare", "if", ["forall", "'a",
		["->", "bool",
			["->", ["thunk", "'a"],
				["->", ["thunk", "'a"], "'a"]]]]],
	["declare", "then", ["forall", "'a", ["->", "'a", ["thunk", "'a"]]]],
	["declare", "else", ["forall", "'a", ["->", "'a", ["thunk", "'a"]]]],
	["declare", "not", ["->", "bool", "bool"]],
	["declare", "odd?", ["->", "int", "bool"]],
	["declare", "even?", ["->", "int", "bool"]],

	// ["define", "odd?", "x", ["if", ["==", "x", "0"],
	// 	["then", "false"],
	// 	["else", ["even?", ["-", "x", "1"]]]]],
	// ["define", "even?", "x", ["if", ["==", "x", "0"],
	// 	["then", "true"],
	// 	["else", ["odd?", ["-", "x", "1"]]]]],

	["declare", "id", ["forall", "'a", ["->", "'a", "'a"]]],
	// ["define", "id", "a", "a"],
	["declare", "id_i", ["->", "int", "int"]],
	// ["define", "id_i", "a", "a"],
	["declare", "id_narrow", ["forall", "'a", ["->", "'a", "'a"]]],
	// ["define", "id_narrow", "a", ["id_i", "a"]],

	// ["define", "length", "a",
	// 	["if", ["empty?", "a"],
	// 		["then", "0"],
	// 		["else", ["+", "1", ["length", ["cdr", "a"]]]]]],
	// ["define", "sum", "a",
	// 	["if", ["empty?", "a"],
	// 		["then", "0"],
	// 		["else", ["+", ["car", "a"], ["sum", ["cdr", "a"]]]]]],
	// ["declare", "map", ["forall", "'k", "'a", "'b",
	// 	["->", ["->", "'a", "'b"],
	// 		["->", ["'k", "'a"], ["'k", "'b"]]]]],
	// ["define", "map", "f", "a",
	// 	["if", ["empty?", "a"],
	// 		["then", ["newlist", "nothing"]],
	// 		["else", ["begin",
	// 			["define", "head", ["f", ["car", "a"]]],
	// 			["define", "rear", ["map", "f", ["cdr", "a"]]],
	// 			["cons", "head", "rear"]]]]],
	// ["declare", "+?", ["forall", "'a", "'b", "'c",
	// 	["->", "'a", ["->", "'b", "'c"]]]],
	// ["define", "main",
	// 	["begin",
	// 		["define", "f", "x", "x"],
	// 		["f", "0"],
	// 		["f", "nothing"],
	// 		["map", ["lambda", "x", "x"], ["cons", "nothing", ["newlist", "nothing"]]]]]
	["let",
		["idx", "x", "x"],
		["::", "map", ["forall", "'k", "'a", "'b",
			["->", ["->", "'a", "'b"],
				["->", ["'k", "'a"], ["'k", "'b"]]]]],
		["map", "f", "a",
			["if", ["empty?", "a"],
				["then", ["newlist", "nothing"]],
				["else", ["let",
					["head", ["f", ["car", "a"]]],
					["rear", ["map", "f", ["cdr", "a"]]],
					["cons", "head", "rear"]]]]],
		["2", ["+", "1", "1"]],
		["begin",
			["idx", "1"],
			["idx", "nothing"],
			["map", ["lambda", "x", "x"], ["cons", "nothing", ["newlist", "nothing"]]]]]
];
const forms = program.map(inference.translate);
const env = new inference.Environment(null);
forms.forEach(p => p.inference(env));
const maindef = env.variables.get("main");
const f_main_mat = forms[forms.length - 1].materialize(new Map(), env);
const matform = f_main_mat;
console.log(matform);
/*
for (let [k, v] of env.variables.entries()) {
	if (!(v.type instanceof type.Polymorphic)) {
		if (v.form) {
			console.log("monomorphic define".yellow, k, "::", v.type, "\n =", v.form);
		} else {
			console.log("monomorphic native".yellow, k, "::", v.type);
		}
	} else if (v.materialized.size) {
		for (let [mangler, f] of v.materialized) {
			if (f.typing) {
				console.log("materialized define".yellow, k, "/".blue, mangler.blue, "::", f.typing.type, "\n =", f);
			} else {
				console.log("materialized native".yellow, k, "/".blue, mangler.blue);
			}
		}
	}
}
*/
