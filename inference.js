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

// A lambda abstraction \parameter.body
class Abstraction extends Form {
	constructor(parameter, body) {
		super();
		this.parameter = parameter;
		this.body = body;
	}
	inference(env) {
		const e = new Environment(env);
		const alpha = newtype("A");
		const beta = newtype("B");
		const fntype0 = type.arrow(alpha, beta);
		// Assign the type to the sub-environment as alpha -> beta
		e.variables.set(this.parameter.name, alpha);
		e.typeslots.set(beta, this.body.inference(e));
		const fnType = fntype0.applySub(e.typeslots);
		return fnType;
	}
	inspect() {
		return "\\" + this.parameter.inspect() + ". " + this.body.inspect();
	}
}
// Term definition, recursive and polymorphic
class Definition extends Form {
	constructor(name, body) {
		super();
		this.name = name;
		this.argument = body;
	}
	inference(env) {
		// Infering definitions ALLOW usage of polymorphism.
		const e = new Environment(env);
		const alpha = newtype("D");
		e.variables.set(this.name, alpha);
		const argtype = this.argument.inference(e).applySub(e.typeslots);
		const fsm = new Set();
		argtype.getFreeSlots(e.typeslots, fsm);
		if (fsm.size) {
			const polytype = new type.Polymorphic(fsm, argtype);
			env.variables.set(this.name, polytype);
			return polytype.instance(newtype);
		} else {
			env.variables.set(this.name, argtype);
		}
	}
	inspect() {
		return "define " + this.name + " = " + this.argument.inspect();
	}
}
// Plain assignment, monomorphic
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
// Recursive assignment, monomorphic
class AssignRec extends Form {
	constructor(name, p) {
		super();
		this.name = name;
		this.argument = p;
	}
	inference(env) {
		const e = new Environment(env);
		const alpha = newtype("D");
		e.variables.set(this.name, alpha);
		const t = this.argument.inference(e);
		env.variables.set(this.name, t);
		return t;
	}
	inspect() {
		return "set rec " + this.name + " = " + this.argument.inspect();
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
		if (a[0] === "define" && a.length === 3) {
			return new Definition(a[1], translate(a[2]));
		} else if (a[0] === "define") {
			return new Definition(a[1], translate(["lambda"].concat(a.slice(2))));
		} else if (a[0] === "let" && a.length === 3) {
			return new Assign(a[1], translate(a[2]));
		} else if (a[0] === "letf" && a.length === 4) {
			return new AssignRec(a[1], new Abstraction(translate(a[2]), translate(a[3])));
		} else if (a[0] === "lambda" && a.length >= 3) {
			const fn0 = translate(a[a.length - 1]);
			return a.slice(1, -1).reduceRight((fn, term) => new Abstraction(translate(term), fn), fn0);
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
	["define", "crz", "x", "y", "z",
		["seq", "x", ["seq", "y", "z"]]]);
const f_length = translate(
	["define", "length", "a",
		["if", ["empty?", "a"],
			["hold", "0"],
			["hold", ["+", "1", ["length", ["cdr", "a"]]]]]]);
const f_sum = translate(
	["define", "sum", "a",
		["if", ["empty?", "a"],
			["hold", "0"],
			["hold", ["+", ["car", "a"], ["sum", ["cdr", "a"]]]]]]);
const f_map = translate(
	["define", "map", "f", "a",
		["if", ["empty?", "a"],
			["hold", ["newlist", "nothing"]],
			["hold", ["cons",
				["f", ["car", "a"]],
				["map", "f", ["cdr", "a"]]]]]]);
const f_mapcrz = translate(
	["define", "map_crz", ["map", "crz"]]
);

console.log(f_map);

const foo = translate(
	["define", "foo", "f",
		["f", "+", ["f", "0"], ["f", "1"]]]);

f_id.inference(env);
f_length.inference(env);
f_sum.inference(env);
f_map.inference(env);
f_mapcrz.inference(env);
// foo.inference(env); // Should be an error
console.log(env.variables);
