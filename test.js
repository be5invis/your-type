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
	["define", "odd?", "x", ["if", ["==", "x", "0"],
		["then", "false"],
		["else", ["even?", ["-", "x", "1"]]]]],
	["define", "even?", "x", ["if", ["==", "x", "0"],
		["then", "true"],
		["else", ["odd?", ["-", "x", "1"]]]]],

	["declare", "id", ["forall", "'a", ["->", "'a", "'a"]]],
	["define", "id", "a", "a"],
	["declare", "id_i", ["->", "int", "int"]],
	["define", "id_i", "a", "a"],
	["declare", "id_narrow", ["forall", "'a", ["->", "'a", "'a"]]],
	["define", "id_narrow", "a", ["id_i", "a"]],

	["define", "length", "a",
		["if", ["empty?", "a"],
			["then", "0"],
			["else", ["+", "1", ["length", ["cdr", "a"]]]]]],
	["define", "sum", "a",
		["if", ["empty?", "a"],
			["then", "0"],
			["else", ["+", ["car", "a"], ["sum", ["cdr", "a"]]]]]],
	["declare", "map", ["forall", "'k", "'a", "'b",
		["->", ["->", "'a", "'b"],
			["->", ["'k", "'a"], ["'k", "'b"]]]]],
	["define", "map", "f", "a",
		["if", ["empty?", "a"],
			["then", ["newlist", "nothing"]],
			["else", ["begin",
				["let", "head", ["f", ["car", "a"]]],
				["let", "rear", ["map", "f", ["cdr", "a"]]],
				["cons", "head", "rear"]]]]],
	["declare", "+?", ["forall", "'a", "'b", "'c",
		["->", "'a", ["->", "'b", "'c"]]]],
	["define", "main",
		["begin",
			["even?", "1"],
			["id", "id", "id", "id", "0"],
			["::", "map", ["->", ["->", "int", "int"], ["->", ["list", "int"], ["list", "int"]]]],
			["::",
				["map", ["lambda", "x", ["+?", "x", "1"]], ["cons", "0", ["newlist", "nothing"]]],
				["list", "int"]],
			["sum", ["cons", "0", ["newlist", "nothing"]]],
			["map", ["lambda", "x", "x"], ["cons", "nothing", ["newlist", "nothing"]]]]]
];

const env = new inference.Environment(null);
program.forEach(p => inference.translate(p).inference(env));
const f_main_mat = env.variables.get("main").form.materialize(new Map(), env);
env.variables.get("main").form = f_main_mat;

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
