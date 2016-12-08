const inference = require("./inference");
const type = require("./type");


const program = [
	["declare", "seq", ["forall", ["'a", "'b"], ["->", "'a", ["->", "'b", "'b"]]]],
	["declare", "car", ["forall", ["'a"], ["->", ["list", "'a"], "'a"]]],
	["declare", "cdr", ["forall", ["'a"], ["->", ["list", "'a"], ["list", "'a"]]]],
	["declare", "cons", ["forall", ["'a"], ["->", "'a", ["->", ["list", "'a"], ["list", "'a"]]]]],
	["declare", "newlist", ["forall", ["'a"], ["->", "unit", ["list", "'a"]]]],
	["declare", "empty?", ["forall", ["'a"], ["->", ["list", "'a"], "bool"]]],
	["declare", "0", "int"],
	["declare", "1", "int"],
	["declare", "true", "bool"],
	["declare", "false", "bool"],
	["declare", "nothing", "unit"],
	["declare", "+", ["forall", ["'a"],
		["->", "'a", ["->", "'a", "'a"]]]],
	["declare", "-", ["forall", ["'a"],
		["->", "'a", ["->", "'a", "'a"]]]],
	["declare", "==", ["forall", ["'a"],
		["->", "'a", ["->", "'a", "bool"]]]],
	["declare", "if", ["forall", ["'a"],
		["->", "bool",
			["->", ["thenT", "'a"],
				["->", ["elseT", "'a"], "'a"]]]]],
	["declare", "then", ["forall", ["'a"], ["->", "'a", ["thenT", "'a"]]]],
	["declare", "else", ["forall", [ "'a"], ["->", "'a", ["elseT", "'a"]]]],
	["declare", "not", ["->", "bool", "bool"]],
	["declare", "odd?", ["->", "int", "bool"]],
	["declare", "even?", ["->", "int", "bool"]],
	["declare", "hetero", ["list", ["any", "'a"]]],

	["let",
		["::", "strange", ["any", "'a"]],
		["strange", "1"],
		[["idx", "x"], "x"],
		["::", "map", ["forall", ["'k", "'a", "'b"],
			["->", ["->", "'a", "'b"],
				["->", ["'k", "'a"], ["'k", "'b"]]]]],
		[["map", "f", "a"],
			["if", ["empty?", "a"],
				["then", ["newlist", "nothing"]],
				["else", ["let",
					["head", ["f", ["car", "a"]]],
					["rear", ["map", "f", ["cdr", "a"]]],
					["cons", "head", "rear"]]]]],
		[["length", "a"],
			["if", ["empty?", "a"],
				["then", "0"],
				["else", ["+", "1", ["length", ["cdr", "a"]]]]]],
		["2", ["+", "1", "1"]],
		[["odd?", "x"], ["if", ["==", "x", "0"], ["then", "false"], ["else", ["even?", ["-", "x", "1"]]]]],
		[["even?", "x"], ["if", ["==", "x", "0"], ["then", "true"], ["else", ["odd?", ["-", "x", "1"]]]]],
		["begin",
			["idx", "strange"],
			["::", "idx", ["->", "float", "float"]],
			// ["map", ["lambda", "x", ["+", "x", "1"]], ["cons", "nothing", ["newlist", "nothing"]]]]] // should error
			["map", ["lambda", "x", ["::", ["+", "x", "1"], "int"]], ["cons", "1", ["newlist", "nothing"]]],
			["map", ["lambda", "x", "x"], "hetero"],
			["length", "hetero"]]]
];
const forms = program.map(inference.translate);
const env = new inference.Environment(null);
forms.forEach(p => p.inference(env));
const maindef = env.variables.get("main");
const f_main_mat = forms[forms.length - 1].materialize(new Map(), env);
const matform = f_main_mat;
console.log(matform);
