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

// Errors
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

// A variable definition.
class VariableDefinition {
	constructor(type, form, defenv) {
		this.type = type; // Its type
		this.form = form; // When present, means that this variable is assigned to a function definition and can be materialized
		this.defenv = defenv; // Its defining environment
		this.materialized = new Map(); // Its materialized versions, mangler -> form
	}
	inspect() {
		return util.inspect({type: this.type, form: this.form, materialized: this.materialized});
	}
	materialize(name, mangle, m) {
		// Materialize a definition body.
		// When it is already mangled, do nothing
		if (this.type instanceof type.Polymorphic) {
			if (!this.materialized.has(mangle)) {
				this.materialized.set(mangle, null);
				this.materialized.set(mangle, this.form.materialize(m, this.defenv));
			}
			return new MangledId(name, mangle);
		} else {
			if (!this.materialized.has("*")) {
				this.materialized.set("*", null);
				this.materialized.set("*", this.form = this.form.materialize(m, this.defenv));
			}
			return new Id(name);
		}
	}
}

// Type assignments
class TypeAssignment {
	constructor(type, instanceAssignments) {
		this.type = type;
		this.instanceAssignments = instanceAssignments;
	}
}
// Environment
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
	setVariable(name, type, form, env) {
		this.variables.set(name, new VariableDefinition(type, form, env));
	}
}



// Program Form
class Form {
	constructor() {
		this.typing = null;
	}
	inspect() {}
	inference() {}
	materialize(m, env) {}
	materializeTypeOf(m, env) {
		if (!this.typing) {
			throw new Error(`${util.inspect(this)} is not typed.`)
		}
		let t = this.typing.type.applySub(env.typeslots).applySub(m);
		if (t instanceof type.Polymorphic) {
			throw new Error(`${util.inspect(this)} is not polymorphic.`)
		}
		if (!t.isClosed()) {
			throw new Error(`The type of <${util.inspect(this)}> is not closed: ${util.inspect(t)} .`);
		}
		return t;
	}
}
// Forward declaration
class ForwardDeclaration {
	constructor(name, type) {
		this.name = name;
		this.type = type;
	}
	inspect() {
		return this.name + "::" + this.type.inspect();
	}
	inference(env) {
		env.setVariable(this.name, this.type, new Native(this.name), env);
		return type.prim("unit");
	}
}
// Identifier
class Id extends Form {
	constructor(name) {
		super();
		this.name = name;
	}
	inference(env) {
		let id = env.lookup(this.name);
		if (!id) throw new VariableNotFoundError(this.name);

		let r = id.type, instanceAssignments = null;
		// Create an instance if its type is polymorphic
		if (r instanceof type.Polymorphic) {
			const inst = r.instance(newtype);
			r = inst.type;
			instanceAssignments = inst.variables;
		}
		this.typing = new TypeAssignment(r, instanceAssignments);
		return r;
	}
	inspect() {
		return this.name;
	}
	materialize(m, env) {
		let vDef = env.lookup(this.name);
		const t = this.materializeTypeOf(m, env);
		if (vDef && vDef.form) {
			// this variable is a function definition.
			// materialize it.
			const idTyping = this.typing;

			if (vDef.type instanceof type.Polymorphic) {
				// It is polymorphic; return an mangled result
				// idTyping.instanceAssignments is always present
				let m1 = new Map();
				for (let [k, v] of idTyping.instanceAssignments) {
					const v1 = v.applySub(env.typeslots).applySub(m);
					if (!v1.isClosed()) {
						throw new Error(`Cannot materialize ${this.name} with a non-closed type ${util.inspect(v1)} assigned to ${util.inspect(k)}.`);
					}
					m1.set(k, v1);
				}
				let n = vDef.materialize(this.name, t.getMangler(), m1);
				n.typing = t;
				return n;
			} else {
				// It is monomorphic; Materialize its content and return
				let n = vDef.materialize(this.name, null, new Map());
				n.typing = t;
				return n;
			}
		} else {
			// Otherwise, it is a plain variable.
			// Materialize it in the simple way.
			let n = new Id(this.name);
			n.typing = new TypeAssignment(t);
			return n;
		}
	}
}
// Mangled identifier
class MangledId extends Id {
	constructor(name, mangler) {
		super(name);
		this.mangler = mangler;
	}
	inference(env) {
		throw new Error("Should not be here.")
	}
	materialize(env) {
		throw new Error("It is already materialized.")
	}
	inspect() {
		return "[".blue + this.name + "/".blue + this.mangler.blue + "]".blue;
	}
}
// Application
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
		this.typing = new TypeAssignment(tresult, null);
		return tresult;
	}
	inspect() {
		if (!(this.argument instanceof Id)) {
			return this.fn.inspect() + " (" + this.argument.inspect() + ")";
		} else {
			return this.fn.inspect() + " " + this.argument.inspect();
		}
	}
	materialize(m, env) {
		let n = new Apply(this.fn.materialize(m, env), this.argument.materialize(m, env));
		n.typing = new TypeAssignment(this.materializeTypeOf(m, env));
		return n;
	}
}
// Lambda abstraction, \parameter.body
class Abstraction extends Form {
	constructor(parameter, body) {
		super();
		this.parameter = parameter;
		this.body = body;
		this.derivedEnv = null;
	}
	inference(env) {
		const e = new Environment(env);
		const alpha = newtype("A");
		const beta = newtype("B");
		const fntype0 = type.arrow(alpha, beta);
		// Assign the type to the sub-environment as alpha -> beta
		e.setVariable(this.parameter.name, alpha);
		e.typeslots.set(beta, this.body.inference(e));
		const fnType = fntype0.applySub(e.typeslots);
		this.parameter.typing = new TypeAssignment(alpha.applySub(e.typeslots), null);
		this.typing = new TypeAssignment(fnType, null);
		this.derivedEnv = e;
		return fnType;
	}
	inspect() {
		return "\\" + this.parameter.inspect() + ". " + this.body.inspect();
	}
	materialize(m, env) {
		let n = new Abstraction(
			this.parameter.materialize(m, this.derivedEnv),
			this.body.materialize(m, this.derivedEnv));
		n.typing = new TypeAssignment(this.materializeTypeOf(m, env));
		return n;
	}
}
// Term definition, recursive and polymorphic
class Definition extends Form {
	constructor(name, body) {
		super();
		this.name = name;
		this.argument = body;
		this.derivedEnv = null;
	}
	inference(env) {
		// Infering definitions ALLOW usage of polymorphism.
		const e = new Environment(env);
		const alpha = newtype("D");
		e.setVariable(this.name, alpha, null);
		let argtype = this.argument.inference(e).applySub(e.typeslots);

		let freeSlots = new Set();
		argtype.getFreeSlots(e.typeslots, freeSlots); // grab the free slots of argtype
		if (freeSlots.size) { // argtype is polymorphic
			let polytype = new type.Polymorphic(freeSlots, argtype);

			// Check whether *argtype* is compatible with *forwardDef.type*
			let forwardDef = env.lookup(this.name);
			if (forwardDef && env === forwardDef.defenv) {
				let forwardType = forwardDef.type;
				if (!(forwardType instanceof type.Polymorphic) // the declared type is polymorphic
					|| forwardType.quantifier.size !== freeSlots.size // they share the same quantity of quantifiers
					|| !type.unify(env.typeslots, argtype, forwardType.instance(newtype).type)) { // and compatible
					throw new TypeIncompatibleError(this.argument, forwardType, argtype, this);
				}
				// If check, rebuild the polymorphic type *polytype*
				argtype = argtype.applySub(env.typeslots); // apply substitutions produced by *unify*
				freeSlots = new Set();
				argtype.getFreeSlots(e.typeslots, freeSlots);
				polytype = new type.Polymorphic(freeSlots, argtype);
			}

			env.setVariable(this.name, polytype, this.argument, env);
			const rettype = polytype.instance(newtype).type;
			this.typing = new TypeAssignment(rettype);
			this.derivedEnv = e;
			return rettype;
		} else {
			// argtype is monomorphic
			// Check whether *argtype* is compatible with *forwardDef.type*
			let forwardDef = env.lookup(this.name);
			if (forwardDef && env === forwardDef.defenv) {
				let forwardType = forwardDef.type;
				if (forwardType instanceof type.Polymorphic // the declared type is monomorphic
					|| !type.unify(env.typeslots, argtype, forwardType)) { // and compatible
					throw new TypeIncompatibleError(this.argument, forwardType, argtype, this);
				}
				argtype = argtype.applySub(env.typeslots); // apply substitutions produced by *unify*
			}

			env.setVariable(this.name, argtype, this.argument, env);
			this.typing = new TypeAssignment(argtype);
			this.derivedEnv = e;
			return argtype;
		}
	}
	inspect() {
		return "define ".yellow + this.name + " = " + this.argument.inspect();
	}
	materialize(m, env) {
		let n = new Definition(this.name, this.argument.materialize(m, this.derivedEnv));
		n.typing = new TypeAssignment(this.materializeTypeOf(m, env));
		return n;
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
		const argtype = this.argument.inference(env);
		env.setVariable(this.name, argtype, null);
		this.typing = new TypeAssignment(argtype);
		return argtype;
	}
	inspect() {
		return "set ".yellow + this.name + " = " + this.argument.inspect();
	}
	materialize(m, env) {
		let n = new Assign(this.name, this.argument.materialize(m, env));
		n.typing = new TypeAssignment(this.materializeTypeOf(m, env));
		return n;
	}
}
// Recursive assignment, monomorphic
class AssignRec extends Form {
	constructor(name, p) {
		super();
		this.name = name;
		this.argument = p;
		this.derivedEnv = null;
	}
	inference(env) {
		const e = new Environment(env);
		const alpha = newtype("D");
		e.setVariable(this.name, alpha, null);
		const argtype = this.argument.inference(e);
		env.setVariable(this.name, argtype, null);
		this.typing = new TypeAssignment(argtype);
		this.derivedEnv = e;
		return argtype;
	}
	inspect() {
		return "set rec ".yellow + this.name + " = " + this.argument.inspect();
	}
	materialize(m, env) {
		let n = new Assign(this.name, this.argument.materialize(m, this.derivedEnv));
		n.typing = new TypeAssignment(this.materializeTypeOf(m, env));
		return n;
	}
}
// Special node, Native
class Native extends Form {
	constructor(name) {
		super();
		this.name = name;
	}
	inspect() {
		return "[native " + this.name + "]";
	}
	materialize(m, env) {
		return new Native(this.name);
	}
}

const env = new Environment(null);

function translateType(a) {
	if (a instanceof Array) {
		if (a[0] === "forall") {
			return new type.Polymorphic(
				new Set(a.slice(1, -1).map(translateType)),
				translateType(a[a.length - 1])
			);
		} else if (a.length === 2) {
			return new type.cmpt(translateType(a[0]), translateType(a[1]));
		} else {
			return new type.cmpt(translateType(a.slice(0, -1)), translateType(a[a.length - 1]));
		}
	} else if (a[0] === "'") {
		return type.slot(a.slice(1));
	} else {
		return type.prim(a);
	}
}
function translate(a) {
	if (a instanceof Array) {
		if (a[0] === "define" && a.length === 3) {
			return new Definition(a[1], translate(a[2]));
		} else if (a[0] === "declare") {
			return new ForwardDeclaration(a[1], translateType(a[2]));
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
			return translate(a.slice(1).reduceRight((y, x) => ["seq", x, y]));
		} else if (a.length === 2) {
			return new Apply(translate(a[0]), translate(a[1]));
		} else {
			return new Apply(translate(a.slice(0, a.length - 1)), translate(a[a.length - 1]));
		}
	} else {
		return new Id(a);
	}
}

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
	["define", "length", "a",
		["if", ["empty?", "a"],
			["then", "0"],
			["else", ["+", "1", ["length", ["cdr", "a"]]]]]],
	["define", "sum", "a",
		["if", ["empty?", "a"],
			["then", "0"],
			["else", ["+", ["car", "a"], ["sum", ["cdr", "a"]]]]]],
	["define", "map", "f", "a",
		["if", ["empty?", "a"],
			["then", ["newlist", "nothing"]],
			["else", ["begin",
				["let", "head", ["f", ["car", "a"]]],
				["let", "rear", ["map", "f", ["cdr", "a"]]],
				["cons", "head", "rear"]]]]],
	["define", "main",
		["begin",
			["even?", "1"],
			["id", "id", "id", "id", "0"],
			["map", ["lambda", "x", ["+", "x", "1"]], ["cons", "0", ["newlist", "nothing"]]],
			["sum", ["cons", "0", ["newlist", "nothing"]]],
			["map", ["lambda", "x", "x"], ["cons", "nothing", ["newlist", "nothing"]]]]]
];

program.forEach(p => translate(p).inference(env));

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
