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
			["::", "idx", ["->", "float", "float"]],
			["map", ["lambda", "x", "x"], ["cons", "nothing", ["newlist", "nothing"]]]]]
];
const forms = program.map(inference.translate);
const env = new inference.Environment(null);
forms.forEach(p => p.inference(env));
const maindef = env.variables.get("main");
const f_main_mat = forms[forms.length - 1].materialize(new Map(), env);
const matform = f_main_mat;
console.log(matform);
