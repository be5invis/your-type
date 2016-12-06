const type = require("./type");
const util = require("util");
require("colors");

const newtype = function () {
	let N = 0;
	return function (name) {
		return type.slot((name || "") + (N++));
	};
}();
const newvar = function () {
	let N = 0;
	return function (name) {
		return ((name || "t") + (N++));
	};
}();

class Environment {
	constructor(parent) {
		this.parent = parent;
		this.variables = new Map();
		this.typeslots = parent ? parent.typeslots : new Map();
	}
	lookup(name) {
		if (this.variables.has(name)) return this.variables.get(name);
		else if (!this.parent) return null;
		else return this.parent.lookup(name);
	}
}


class TypeIncompatibleError extends Error {
	constructor(form, desired, resulted, context) {
		super();
		this.form = form;
		this.desired = desired;
		this.resulted = resulted;
		this.context = context;
		this.message = `Type incompatible for ${util.inspect(form).green} :
	Expected ${util.inspect(desired)}.
	Got      ${util.inspect(resulted)}.
	Found in ${util.inspect(context).green}`;
	}
}
class VariableNotFoundError extends Error {
	constructor(name) {
		super();
		this.name = name;
		this.message = `Variable ${name} does not exist`;
	}
}

class Form {
	constructor() {}
	inspect() {}
}

class Id extends Form {
	constructor(name) {
		super();
		this.name = name;
	}
	inference(env) {
		const r = env.lookup(this.name);
		if (!r) throw new VariableNotFoundError(this.name);
		// Create an instance if its type is polymorphic
		if (r instanceof type.Polymorphic) {
			return r.instance(newtype);
		} else {
			return r;
		}
	}
	inspect() {
		return this.name;
	}
}

class Apply extends Form {
	constructor(p, q) {
		super();
		this.fn = p;
		this.argument = q;
	}
	inference(env) {
		const tfn = this.fn.inference(env).applySub(env.typeslots);
		const targ = this.argument.inference(env).applySub(env.typeslots);

		const s = newtype();
		const t = newtype();
		const psuidoArrow = type.arrow(s, t);
		if (!type.unify(env.typeslots, psuidoArrow, tfn)) {
			throw new Error(`Type of ${this.fn.inspect()} is not a function : ${tfn.applySub(env.typeslots).inspect()}`);
		}

		const targ1 = s.applySub(env.typeslots);
		if (!type.unify(env.typeslots, targ1, targ)) {
			throw new TypeIncompatibleError(
				this.argument,
				targ1.applySub(env.typeslots),
				targ.applySub(env.typeslots),
				this);
		}

		const tresult = t.applySub(env.typeslots);
		return tresult;
	}
	inspect() {
		if (!(this.argument instanceof Id)) {
			return this.fn.inspect() + " (" + this.argument.inspect() + ")";
		} else {
			return this.fn.inspect() + " " + this.argument.inspect();
		}
	}
}

class FDef extends Form {
	constructor(name, p, q, local) {
		super();
		this.name = name;
		this.parameter = p;
		this.body = q;
		this.local = !!local;
	}
	inference(env) {
		const e = new Environment(env);
		const alpha = newtype("A");
		const beta = newtype("B");
		const fntype0 = type.arrow(alpha, beta);
		// Assign the type to the sub-environment as alpha -> beta
		e.variables.set(this.parameter.name, alpha);
		e.variables.set(this.name, type.arrow(alpha, beta));
		e.typeslots.set(beta, this.body.inference(e));
		const fnType = fntype0.applySub(e.typeslots);
		if (this.local) { // If the function is embedded, do not return a polymorphic result
			env.variables.set(this.name, fnType);
			return fnType;
		} else { // otherwise, return polymorphic
			const fsm = new Set();
			fnType.getFreeSlots(e.typeslots, fsm);
			const polytype = new type.Polymorphic(fsm, fnType);
			env.variables.set(this.name, polytype);
			return polytype.instance(newtype);
		}
	}
	inspect() {
		return "function " + this.name + " " + this.parameter.inspect() + " = " + this.body.inspect();
	}
}

class Assign extends Form {
	constructor(name, p) {
		super();
		this.name = name;
		this.argument = p;
	}
	inference(env) {
		const t = this.argument.inference(env);
		env.variables.set(this.name, t);
		return t;
	}
	inspect() {
		return "set " + this.name + " = " + this.argument.inspect();
	}
}

const env = new Environment(null);
// This is a prelude
// call : forall a b. (a -> b) -> a -> b;
env.variables.set("call",
	new type.Polymorphic(
		new Set([type.slot("a"), type.slot("b")]),
		type.arrow(type.arrow(type.slot("a"), type.slot("b")), type.arrow(type.slot("a"), type.slot("b")))
	));
// seq : forall a b. a -> b -> b
env.variables.set("seq",
	new type.Polymorphic(
		new Set([type.slot("a"), type.slot("b")]),
		type.arrow(type.slot("a"), type.arrow(type.slot("b"), type.slot("b")))
	));
// car : forall a. list a -> a
env.variables.set("car",
	new type.Polymorphic(
		new Set([type.slot("a")]),
		type.arrow(type.cmpt(type.prim("list"), type.slot("a")), type.slot("a"))
	));
// cdr : forall a. list a -> list a
env.variables.set("cdr",
	new type.Polymorphic(
		new Set([type.slot("a")]),
		type.arrow(type.cmpt(type.prim("list"), type.slot("a")), type.cmpt(type.prim("list"), type.slot("a")))
	));
// cons : forall a. a -> list a -> list a
env.variables.set("cons",
	new type.Polymorphic(
		new Set([type.slot("a")]),
		type.arrow(
			type.slot("a"),
			type.arrow(
				type.cmpt(type.prim("list"), type.slot("a")),
				type.cmpt(type.prim("list"), type.slot("a"))))
	));
// newlist : forall a. unit -> list a
env.variables.set("newlist",
	new type.Polymorphic(
		new Set([type.slot("a")]),
		type.arrow(
			type.prim("unit"),
			type.cmpt(type.prim("list"), type.slot("a")))
	));
// empty? : forall a. list a -> bool
env.variables.set("empty?",
	new type.Polymorphic(
		new Set([type.slot("a")]),
		type.arrow(type.cmpt(type.prim("list"), type.slot("a")), type.prim("bool"))
	));
// 0 and 1
env.variables.set("0", type.prim("int"));
env.variables.set("1", type.prim("int"));
env.variables.set("nothing", type.prim("unit"));
// +
env.variables.set("+",
	type.arrow(type.prim("int"),
		type.arrow(type.prim("int"), type.prim("int"))));
// if : forall a. bool -> thunk a -> thunk a -> a
env.variables.set("if",
	new type.Polymorphic(
		new Set([type.slot("a")]),
		type.arrow(type.prim("bool"),
			type.arrow(type.cmpt(type.prim("thunk"), type.slot("a")),
				type.arrow(type.cmpt(type.prim("thunk"), type.slot("a")), type.slot("a"))))));
// hold : forall a. a -> thunk a
env.variables.set("hold",
	new type.Polymorphic(
		new Set([type.slot("a")]),
		type.arrow(type.slot("a"),
			type.cmpt(type.prim("thunk"), type.slot("a")))));

function translate(a) {
	if (a instanceof Array) {
		if (a[0] === "function") {
			return new FDef(a[1], translate(a[2]), translate(a[3]));
		} else if (a[0] === "let" && a.length === 3) {
			return new Assign(a[1], translate(a[2]));
		} else if (a[0] === "letf" && a.length === 4) {
			return new FDef(a[1], translate(a[2]), translate(a[3]), true);
		} else if (a[0] === "lambda") {
			const t = newvar();
			return translate(["seq", ["letf", t, a[1], a[2]], t]);
		} else if (a[0] === "begin") {
			return translate(a.slice(1).reduce((x, y) => ["seq", x, y]));
		} else if (a.length === 2) {
			return new Apply(translate(a[0]), translate(a[1]));
		} else {
			return new Apply(translate(a.slice(0, a.length - 1)), translate(a[a.length - 1]));
		}
	} else {
		return new Id(a);
	}
}

const f_id = translate(
	["function", "crz", "x", ["seq",
		["letf", "crz1", "y", ["seq",
			["letf", "crz2", "z",
				["seq", "x", ["seq", "y", "z"]]],
			"crz2"]
		],
		"crz1"]]);
const f_length = translate(
	["function", "length", "a",
		["if", ["empty?", "a"],
			["hold", "0"],
			["hold", ["+", "1", ["length", ["cdr", "a"]]]]]]);
const f_sum = translate(
	["function", "sum", "a",
		["if", ["empty?", "a"],
			["hold", "0"],
			["hold", ["+", ["car", "a"], ["sum", ["cdr", "a"]]]]]]);
const f_map = translate(
	["function", "map", "f", ["begin",
		["lambda", "a", ["if", ["empty?", "a"],
			["hold", ["newlist", "nothing"]],
			["hold", ["cons",
				["f", ["car", "a"]],
				["map", "f", ["cdr", "a"]]]]]]]]);

const foo = translate(
	["function", "foo", "f",
		["f", "+", ["f", "0"], ["f", "1"]]]);

f_id.inference(env);
f_length.inference(env);
f_sum.inference(env);
f_map.inference(env);
// foo.inference(env); // Should be an error
console.log(env.variables);
