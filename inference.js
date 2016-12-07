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
		console.log("Materialize", name, m);
		// Materialize a definition body.
		// When it is already mangled, do nothing
		if (this.type instanceof type.Polymorphic) {
			if (!this.materialized.has(mangle)) {
				this.materialized.set(mangle, null);
				this.materialized.set(mangle, this.form.materialize(m, this.defenv));
			}
			return new MangledId(name, mangle);
		} else {
			if (!this.materialized.has("")) {
				this.materialized.set("", null);
				this.materialized.set("", this.form = this.form.materialize(m, this.defenv));
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
	* names() {
		yield*this.variables.entries();
		if (this.parent) {
			yield*this.parent.names();
		}
	}
}



// Program Form
class Form {
	constructor() {
		this.typing = null;
	}
	inspect() {}
	inference() {}
	materialize(m, env) {
		try {
			return this._materialize(m, env);
		} catch(e) {
			console.log(this);
			throw e;
		}
	}
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
class ForwardDeclaration extends Form {
	constructor(name, type) {
		super();
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
// Limitation expression
class Limitation extends Form {
	constructor(argument, type) {
		super();
		this.argument = argument;
		this.type = type;
	}
	inspect() {
		return this.argument + "::" + this.type.inspect();
	}
	inference(env) {
		let t = (this.type instanceof type.Polymorphic
			? this.type.instance(newtype).type
			: this.type).applySub(env.typeslots);
		env.setVariable(this.name, this.type, new Native(this.name), env);
		let t1 = this.argument.inference(env);

		if (!type.unify(env.typeslots, t, t1)) {
			throw new TypeIncompatibleError(
				this.argument,
				t.applySub(env.typeslots),
				t1.applySub(env.typeslots),
				this);
		}

		const tresult = t.applySub(env.typeslots);
		this.typing = new TypeAssignment(tresult, null);
		return tresult;
	}
	_materialize(m, env) {
		return this.argument.materialize(m, env);
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
	_materialize(m, env) {
		let vDef = env.lookup(this.name);
		const t = this.materializeTypeOf(m, env);
		if (vDef && vDef.form) {
			// this variable is a function definition.
			// materialize it.
			const idTyping = this.typing;

			if (vDef.type instanceof type.Polymorphic) {
				// It is polymorphic; return an mangled result
				// idTyping.instanceAssignments is always present
				let m1 = new Map(m);
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
				let n = vDef.materialize(this.name, null, m);
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
	inspect(depth) {
		if (!(this.argument instanceof Id)) {
			return this.fn.inspect(depth) + " (" + this.argument.inspect(depth) + ")";
		} else {
			return this.fn.inspect(depth) + " " + this.argument.inspect(depth);
		}
	}
	_materialize(m, env) {
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
	inspect(depth) {
		return "\\" + this.parameter.inspect(depth) + ". " + this.body.inspect(depth);
	}
	_materialize(m, env) {
		let n = new Abstraction(
			this.parameter.materialize(m, this.derivedEnv),
			this.body.materialize(m, this.derivedEnv));
		n.typing = new TypeAssignment(this.materializeTypeOf(m, env));
		return n;
	}
}

// Recursive binding of terms. May be polymorphic.
class Block extends Form {
	constructor(terms, body) {
		super();
		this.terms = terms;
		this.body = body;
		this.e1 = null;
		this.e2 = null;
	}
	inference(env) {
		// Infering definitions ALLOW usage of polymorphism.
		const e1 = new Environment(env);
		const e2 = new Environment(env);

		// Pass 1: Grab all forward declarations
		let fwdTypes = new Map();
		for (let term of this.terms) {
			const name = term.name;
			const alpha = newtype("D");
			e1.setVariable(name, alpha, null);

			if (term.declareType) {
				fwdTypes.set(name, term.declareType);
			}
		}

		// Pass 2: Inference all bindings
		let decisions = [];
		for (let term of this.terms) {
			const name = term.name;
			const form = term.form;
			if (!form) continue;
			let argtype = form.inference(e1).applySub(e1.typeslots);

			if (fwdTypes.has(name)) {
				let forwardType = fwdTypes.get(name);
				let decType = forwardType;
				if (forwardType instanceof type.Polymorphic) {
					forwardType = forwardType.instance(newtype).type;
				}
				if (!type.unify(e1.typeslots, argtype, forwardType)) {
					throw new TypeIncompatibleError(form, decType, argtype, this);
				}
				argtype = argtype.applySub(e1.typeslots); // apply substitutions produced by *unify*
			}

			decisions.push({
				name: name,
				form: form,
				argtype: argtype
			});
		}

		// Pass 3: Decide the type of each binding
		let existingFreeSlots = new Set();
		for (let [k, v] of env.names()) {
			if (v.type instanceof type.Polymorphic) continue;
			v.type.applySub(env.typeslots).getFreeSlots(env.typeslots, existingFreeSlots);
		}

		for (let {name, form, argtype} of decisions) {
			let freeSlots = new Set();
			argtype.getFreeSlots(e1.typeslots, freeSlots); // grab the free slots of argtype

			for (let s of existingFreeSlots) {
				freeSlots.delete(s);
			}

			if (freeSlots.size) { // argtype is polymorphic
				let polytype = new type.Polymorphic(freeSlots, argtype);
				e2.setVariable(name, polytype, form, e1);
			} else { // argtype is monomorphic
				e2.setVariable(name, argtype, form, e1);
			}
		}

		this.terms = this.terms.filter(x => !!x.form);
		const t = this.body.inference(e2);
		this.typing = new TypeAssignment(t);
		this.e1 = e1;
		this.e2 = e2;
		return t;
	}
	inspect(depth) {
		return "let rec ".yellow
		+ "\n" + "  ".repeat(depth - 1)
		+ this.terms.map(
			(x) => x.form
				? util.inspect(x.name) + " = ".green + x.form.inspect(depth + 1)
				: ""
		).join(";\n" + "  ".repeat(depth - 1))
		+ "\n" + "  ".repeat(depth - 1) + "in ".yellow + this.body.inspect(depth);
	}
	_materialize(m, env) {
		let terms1 = [];
		for (let {name, form} of this.terms) {
			let vd = this.e2.lookup(name);
			if (!(vd.type instanceof type.Polymorphic)) {
				terms1.push({
					name: name,
					form: form.materialize(m, this.e1)
				});
			}
		}
		let n = new Block(terms1, this.body.materialize(m, this.e2));
		n.typing = new TypeAssignment(this.materializeTypeOf(m, env));
		for (let {name, form} of this.terms) {
			let vd = this.e2.lookup(name);
			if (!vd || !vd.materialized.size) continue;
			for (let [mangler, f] of vd.materialized.entries()) {
				if (!mangler) continue;
				terms1.push({
					name: new MangledId(name, mangler),
					form: f
				});
			}
		}
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
	_materialize(m, env) {
		return new Native(this.name);
	}
}

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
function translateBinding(x) {
	if (x[0] === "::") {
		return {
			name: x[1],
			declareType: translateType(x[2])
		};
	} else if (x.length === 2) {
		return {
			name: x[0],
			form: translate(x[1])
		};
	} else {
		return {
			name: x[0],
			form: translate(["lambda"].concat(x.slice(1)))
		};
	}
}
function translate(a) {
	if (a instanceof Array) {
		if (a[0] === "declare") {
			return new ForwardDeclaration(a[1], translateType(a[2]));
		} else if (a[0] === "::") {
			return new Limitation(translate(a[1]), translateType(a[2]));
		} else if (a[0] === "let") {
			return new Block(a.slice(1, -1).map(translateBinding), translate(a[a.length - 1]));
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

exports.Environment = Environment;
exports.translate = translate;
