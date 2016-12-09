const util = require("util");


// //// TYPES
class Type {
	constructor() {}

	/**
	 * Get all meta type variables.
	 * @returns {Map<number, Type>}
	 */
	getMetaSlots() {
		let a = new Map;
		this._getMetaSlots(a);
		return a;
	}
	_getMetaSlots(a) {}
	/**
	 * Get all free slots
	 * @returns{Set<string>}
	 */
	getFreeSlots() {
		let a = new Set;
		let bound = new Set;
		this._getFreeSlots(bound, a);
		return a;
	}
	_getFreeSlots(bound, a) {}
	/**
	 * Get all binders of a type
	 * @returns{Set<string>}
	 */
	getBinders() {
		let a = new Set;
		this._getBinders(a);
		return a;
	}
	_getBinders() {}
	/**
	 * Substitute type variables to a corresponded type.
	 * @param {Map<string, Type>} m
	 * @returns {Type}
	 */
	subst(m) {
		return this;
	}
	/**
	 * Instantiate the topmost for-alls of the argument type with flexible type variables
	 * @param {Environment} env
	 * @returns {Type}
	 */
	instantiate(env) {
		return this;
	}
	/**
	 * Performs deep skolemisation, retuning the skolem constants and the skolemised type
	 * @param {Environment} env
	 * @returns {{map: Map<string, Slot>, type: Type}}
	 */
	skolemise(env) {
		return {
			map: new Map(),
			type: this
		};
	}
	/**
	 * Quantify over the specified type variables
	 * @param {Environment} env
	 * @param {Array<MetaSlotVal>} mvs
	 * @returns {Type}
	 */
	quantify(env, mvs) {
		let usedBinders = this.getBinders();
		let nRef = {val: 0};
		let newBinders = [];
		for (let slot of mvs) {
			let newBinder = new Slot(generateBinder(nRef, usedBinders));
			slot.typeRef.val = newBinder;
			newBinders.push(newBinder);
		}
		return new ForAll(newBinders.map(x => x.name), this.zonk(env));
	}
	/**
	 * Eliminate any substitutions in the type
	 * @param {Environment} env
	 * @returns {Type}
	 */
	zonk(env) {
		return this;
	}
	/**
	 * @param{Environment} env
	 */
	instSigma(env, exp) {
		if (exp.check) {
			return this.subsCheckRho(env, exp.check);
		} else {
			exp.infer.val = this.instantiate(env);
		}
	}
	/**
	 * @param{Environment} env
	 * @param{Type} that
	 */
	subsCheck(env, that) {
		const {map:skolTvs, type:rho2} = this.skolemise(env);
		this.subsCheckRho(env, rho2);
		const escTvs = new Set(env.getAllFreeSlots([this, that]));
		for (let [k, v] of skolTvs) {
			if (escTvs.has(k)) {
				throw "Subsumption check failed"
			}
		}
	}
	/**
	 * @param{Environment} env
	 * @param{Type} that
	 */
	subsCheckRho(env, that) {
		if (that instanceof Composite) {
			const [f1, a1] = unifyComposite(this, env);
			subsCheckComposite(env, f1, that.fn, a1, that.arg);
		}
		return unify(this, that);
	}
}

function subsCheckComposite(env, f1, f2, a1, a2) {
	f1.subsCheck(env, f2);
	a1.subsCheckRho(env, a1);
}

// Generate a new binder
function generateBinder(nRef, used) {
	nRef.val += 1;
	let name = "t" + nRef.val;
	while(used.has(name)){
		nRef.val += 1;
		name = "t" + nRef.val;
	}
	return name;
}

class ForAll extends Type {
	/**
	 * @param {Array<string>} quantifiers
	 * @param {Type} body
	 */
	constructor(quantifiers, body) {
		super();
		this.quantifiers = quantifiers;
		this.body = body;
	}
	_getMetaSlots(a) {
		this.body._getMetaSlots(a);
	}
	_getFreeSlots(bound, a) {
		const b1 = new Set(bound);
		for (let q of this.quantifiers) {
			b1.add(q);
		}
		this.body._getFreeSlots(b1, a);
	}
	_getBinders(a) {
		for (let q of this.quantifiers) {
			a.add(q);
		}
		this.body._getBinders(a);
	}
	subst(m) {
		let m1 = new Map(m);
		for (let q of this.quantifiers) {
			m1.delete(q);
		}
		return new ForAll(this.quantifiers, this.body.subst(m1));
	}
	instantiate(env) {
		let m = new Map();
		for (let q of this.quantifiers) {
			m.set(q, new MetaSlot(env.newMetaSlotVal()));
		}
		return this.body.subst(m);
	}
	skolemise(env) {
		let m = new Map();
		for (let q of this.quantifiers) {
			m.set(q, new Slot(env.newSkolemVariable()));
		}
		let {map: m1, type: t1} = this.body.subst(m).skolemise(env);
		for (let [k, v] of m1.entries()) {
			m.set(k, v);
		}
		return {
			map: m,
			type: t1
		};
	}

	zonk(env) {
		return new ForAll(this.quantifiers, this.body.zonk(env));
	}
	/**
	 * @param{Environment} env
	 * @param{Type} that
	 */
	subsCheckRho(env, that) {
		return this.instantiate(env).subsCheckRho(env, that);
	}
}
class Primitive extends Type {
	/**
	 * @param {string} name
	 */
	constructor(name) {
		super();
		this.name = name;
	}
}
class Slot extends Type {
	/**
	 * @param {string} name
	 */
	constructor(name) {
		super();
		this.name = name;
	}
	_getFreeSlots(bound, a) {
		if (!bound.has(this.name) && !a.has(this.name)) {
			a.add(this.name);
		}
	}
	subst(m) {
		if (m.has(this.name)) {
			return m.get(this.name);
		} else {
			return this;
		}
	}
}
class Composite extends Type {
	/**
	 * @param {Type} fn
	 * @param {Type} arg
	 */
	constructor(fn, arg) {
		super();
		this.fn = fn;
		this.arg = arg;
	}
	_getMetaSlots(a) {
		this.fn._getMetaSlots(a);
		this.arg._getMetaSlots(a);
	}
	_getFreeSlots(bound, a) {
		this.fn._getFreeSlots(bound, a);
		this.arg._getFreeSlots(bound, a);
	}
	_getBinders(a) {
		this.fn._getBinders(a);
		this.arg._getBinders(a);
	}
	subst(m) {
		return new Composite(this.fn.subst(m), this.arg.subst(m));
	}
	skolemise(env) {
		let {map:m1, type:t1} = this.arg.skolemise(env);
		return {
			map: m1,
			type: new Composite(this.fn, t1)
		};
	}
	zonk(env) {
		return new Composite(this.fn.zonk(env), this.arg.zonk(env));
	}
	/**
	 * @param{Environment} env
	 * @param{Type} that
	 */
	subsCheckRho(env, that) {
		const [f2, a2] = unifyComposite(that, env);
		return subsCheckComposite(env, this.fn, f2, this.arg, a2);
	}
}
class MetaSlot extends Type {
	/**
	 * @param {MetaSlotVal} arg - Argument
	 */
	constructor(arg) {
		super();
		this.arg = arg;
	}
	_getMetaSlots(a) {
		if (!a.has(this.arg.id)) {
			a.set(this.arg.id, this.arg);
		}
	}
	zonk(env) {
		if (this.arg.typeRef.val) {
			let t1 = this.arg.typeRef.val.zonk(env);
			this.arg.typeRef.val = t1;
			return t1;
		} else {
			return this;
		}
	}
}
// MetaVal -- can unify with any tau-type
class MetaSlotVal {
	/**
	 * @param {number} id
	 * @param {{val:Type}} typeRef
	 */
	constructor(id, typeRef) {
		this.id = id;
		this.typeRef = typeRef;
	}
	equalTo(that) {
		return that && that instanceof MetaSlotVal && that.id === this.id;
	}
}

// //// Environments
class Environment {
	/**
	 * @param {{val:number}} uniqs
	 * @param {Map<string, Type>} variables
	 */
	constructor(uniqs, variables) {
		this.uniqs = uniqs;
		this.variables = variables;
	}
	/**
	 * Extend a variable
	 * @param {string} name
	 * @param {Type} type
	 */
	extend(name, type) {
		let v1 = new Map(this.variables);
		v1.set(name, type);
		return new Environment(this.uniqs, v1);
	}
	/**
	 * @param {string} name
	 * @returns {Type}
	 */
	lookup(name) {
		if (this.variables.has(name)) {
			return this.variables.get(name);
		} else {
			throw new Error(`Variable ${name} not found.`);
		}
	}
	newUnique() {
		this.uniqs.val += 1;
		return this.uniqs.val;
	}
	newMetaSlotVal() {
		const u = this.newUnique();
		const ref = {val: null};
		return new MetaSlotVal(u, ref);
	}
	newSkolemVariable(s) {
		const u = this.newUnique();
		return "." + u + "." + s;
	}

	getTypes() {
		return this.variables.values();
	}
	/**
	 * @param{IterableIterator<Type>} tys
	 */
	* getMetaSlotVars(tys) {
		for (let type of tys) {
			let type1 = type.zonk(this);
			yield * type1.getMetaSlots();
		}
	}
	/**
	 * @param{IterableIterator<Type>} tys
	 */
	* getAllFreeSlots(tys) {
		for (let type of tys) {
			let type1 = type.zonk(this);
			yield * type1.getFreeSlots();
		}
	}
}

// ////Unification
/**
 * @param {Type} t1
 * @param {Type} t2
 * @returns {boolean}
 */
function unify(t1, t2) {
	if (badtype(t1) || badtype(t2)) throw "Should not be here."
	if (t1 instanceof Slot && t2 instanceof Slot && t1.name === t2.name) return true;
	if (t1 instanceof MetaSlot && t2 instanceof MetaSlot && t1.arg.equalTo(t2.arg)) return true;
	if (t1 instanceof MetaSlot) return unifyVar(t1.arg, t2);
	if (t2 instanceof MetaSlot) return unifyVar(t2.arg, t1);
	if (t1 instanceof Composite && t2 instanceof Composite) {
		unify(t1.fn, t2.fn);
		unify(t2.arg, t2.arg);
		return true;
	}
	if (t1 instanceof Primitive && t2 instanceof Primitive && t1.name === t2.name) {return true;}
	throw "Cannot unify."
}
/**
 * Unify variable
 * @param {MetaSlotVal} msv
 * @param {Type} ty
 */
function unifyVar(msv, ty) {
	if (msv.typeRef.val) {
		return unify(msv.typeRef.val, ty);
	} else {
		return unifyUnbound(msv, ty);
	}
}
/**
 * Unify unbounded type
 * @param {MetaSlotVal} msv
 * @param {Type} ty
 */
function unifyUnbound(msv, ty) {
	if (ty instanceof MetaSlot) {
		let msv2 = ty.arg;
		if (msv2.typeRef.val) {
			return unify(new MetaSlot(msv), msv2.typeRef.val);
		} else {
			msv.typeRef.val = ty;
			return true;
		}
	} else {
		let msvs2 = ty.getMetaSlots();
		if (msvs2.has(msv.id)) {
			throw "Recursive Type."
		} else {
			msv.typeRef.val = ty;
			return true;
		}
	}
}

function FunctionType(arg, body) {
	return new Composite(
		new Composite(new Primitive("->"), arg),
		body
	);
}
/**
 * @param {Type} type
 * @param {Environment} env
 * @returns {[Type, Type]}
 */
function unifyFun(type, env) {
	if (type instanceof Composite && type.fn instanceof Composite && type.fn.fn instanceof Primitive && type.fn.fn.name === "->") {
		return [type.fn.arg, type.arg];
	} else {
		const argMsv = env.newMetaSlotVal();
		const resMsv = env.newMetaSlotVal();
		unify(type, FunctionType(new MetaSlot(argMsv), new MetaSlot(resMsv)));
		return [argMsv, resMsv];
	}
}
/**
 * @param {Type} type
 * @param {Environment} env
 * @returns {[Type, Type]}
 */
function unifyComposite(type, env) {
	if (type instanceof Composite) {
		return [type.fn, type.arg];
	} else {
		const argMsv = env.newMetaSlotVal();
		const resMsv = env.newMetaSlotVal();
		unify(type, new Composite(new MetaSlot(argMsv), new MetaSlot(resMsv)));
		return [argMsv, resMsv];
	}
}
/**
 * @param {Type} t
 * @returns {boolean}
 */
function badtype(t) {
	return t instanceof Slot && t.name[0] !== ".";
}





// //// TERMS
class Term {
	constructor() {}
	isAtomic() {
		return false;
	}
	/**
* 	 * @param {Environment} env
	 */
	checkRho(env, type) {
		return this.tcRho(env, {check: type});
	}
	/**
	 * @param {Environment} env
	 * @returns {Type}
	 */
	inferRho(env) {
		const ref = {val: null};
		this.tcRho(env, {infer: ref});
		if (!ref.val) throw "Cannot decide type"
		return ref.val;
	}
	/**
	 * @param {Environment} env
	 * @param {{check: Type} | {infer: {val: Type}}} exp
	 */
	tcRho(env, exp) {}
	/**
	 * @param{Environment} env
	 */
	inferSigma(env) {
		const expTy = this.inferRho(env);
		const envTys = env.getTypes();
		const envMsvs = env.getMetaSlotVars(envTys);
		const resMsvs = new Map(env.getMetaSlotVars([expTy]));
		for (let [id, v] of envMsvs) {
			resMsvs.delete(id);
		}
		return expTy.quantify(env, Array.from(resMsvs.values()));
	}
	/**
	 * @param{Environment} env
	 * @param{Type} sigma
	 */
	checkSigma(env, sigma) {
		const {map: mvs, type: rho} = sigma.skolemise(env);
		this.checkRho(env, rho);
		const envTys = env.getTypes();
		const escTvs = new Set(env.getAllFreeSlots(envTys));
		for (let [name, slot] of mvs) {
			if (escTvs.has(name)) {
				throw "Type is not polymorphic enough"
			}
		}
	}
}
class Lit extends Term {
	/**
	 * @param {any} n
	 */
	constructor(n) {
		super();
		this.lit = n;
	}
	isAtomic() {
		return true;
	}
	tcRho(env, exp) {
		if (typeof this.lit === "number") {
			return new Primitive("int").instSigma(env, exp);
		} else if (typeof this.lit === "string") {
			return new Primitive("str").instSigma(env, exp);
		} else {
			return new Primitive("unit").instSigma(env, exp);
		}
	}
}
class Var extends Term {
	/**
	 * @param {string} name
	 */
	constructor(name) {
		super();
		this.name = name;
	}
	isAtomic() {
		return true;
	}
	tcRho(env, exp) {
		const ty = env.lookup(this.name);
		return ty.instSigma(env, exp);
	}
}
class App extends Term {
	/**
	 * @param {Term} fn
	 * @param {Term} arg
	 */
	constructor(fn, arg) {
		super();
		this.fn = fn;
		this.arg = arg;
	}
	tcRho(env, exp) {
		const funTy = this.fn.inferRho(env);
		const [argTy, resTy] = unifyFun(funTy, env);
		this.arg.checkSigma(env, argTy);
		return resTy.instSigma(env, exp);
	}
}
/**
 * Lambda abstraction
 */
class Lam extends Term {
	/**
	 * @param {string} param
	 * @param {Term} body
	 */
	constructor(param, body) {
		super();
		this.param = param;
		this.body = body;
	}
	/**
	 * @param{Environment} env
	 */
	tcRho(env, exp) {
		if (exp.check) {
			const [varTy, bodyTy] = unifyFun(exp.check, env);
			const env1 = env.extend(this.param, varTy);
			return this.body.checkRho(env1, bodyTy);
		} else {
			const varTy = new MetaSlot(env.newMetaSlotVal());
			const env1 = env.extend(this.param, varTy);
			const bodyTy = this.body.inferRho(env1);
			exp.infer.val = FunctionType(varTy, bodyTy);
		}
	}
}
/**
 * Lambda abstraction with parameter type annotation
 */
class ALam extends Term {
	/**
	 * @param {string} param
	 * @param {Type} type
	 * @param {Term} body
	 */
	constructor(param, type, body) {
		super();
		this.param = param;
		this.type = type;
		this.body = body;
	}
	/**
	 * @param{Environment} env
	 */
	tcRho(env, exp) {
		if (exp.check) {
			const [varTy, bodyTy] = unifyFun(exp.check, env);
			varTy.subsCheck(this.type);
			const env1 = env.extend(this.param, varTy);
			return this.body.checkRho(env1, bodyTy);
		} else {
			const env1 = env.extend(this.param, this.type);
			const bodyTy = this.body.inferRho(env1);
			exp.infer.val = FunctionType(this.type, bodyTy);
		}
	}
}
class Let extends Term {
	/**
	 * @param {string} name
	 * @param {Term} bind
	 * @param {Term} body
	 */
	constructor(name, bind, body) {
		super();
		this.name = name;
		this.bind = bind;
		this.body = body;
	}
	/**
	 * @param{Environment} env
	 */
	tcRho(env, exp) {
		const varTy = this.bind.inferSigma(env);
		const env1 = env.extend(this.name, varTy);
		return this.body.tcRho(env1, exp);
	}
}
class Ann extends Term {
	/**
	 * @param {Type} type
	 * @param {Term} body
	 */
	constructor(type, body) {
		super();
		this.type = type;
		this.body = body;
	}
	/**
	 * @param{Environment} env
	 */
	tcRho(env, exp) {
		this.body.checkSigma(this.type);
		this.type.instSigma(env, exp);
	}
}

/**
 * @returns{Type}
 */
function translateType(a) {
	if (a instanceof Array) {
		if (a[0] === "forall") {
			return new ForAll(
				a[1].map(x => translateType(x).name),
				translateType(a[2])
			);
		} else if (a.length === 2) {
			return new Composite(translateType(a[0]), translateType(a[1]));
		} else {
			return new Composite(translateType(a.slice(0, -1)), translateType(a[a.length - 1]));
		}
	} else if (a[0] === "'") {
		return new Slot(a.slice(1));
	} else {
		return new Primitive(a);
	}
}

/**
 * @returns{Term}
 */
function translate(a) {
	if (!a) {
		return new Lit(a);
	} else if (a instanceof Array) {
		if (a[0] === "let") {
			return new Let(a[1], translate(a[2]), translate(a[3]));
		} else if (a[0] === "lambda" && a.length >= 3) {
			const fn0 = translate(a[a.length - 1]);
			return a.slice(1, -1).reduceRight((fn, term) => (typeof term === "string")
				? new Lam(term, fn)
				: new ALam(term[0], translateType(term[1]), fn), fn0);
		} else if (a[0] === "begin") {
			return translate(a.slice(1).reduceRight((y, x) => ["seq", x, y]));
		} else if (a.length === 2) {
			return new App(translate(a[0]), translate(a[1]));
		} else {
			return new App(translate(a.slice(0, a.length - 1)), translate(a[a.length - 1]));
		}
	} else if (typeof a === "string") {
		return new Var(a);
	} else {
		return new Lit(a);
	}
}

const env = new Environment({val: 0}, new Map([[
	"&", translateType(["forall", ["'a", "'b"],
		["->", "'a",
			["->", "'b",
				["*", "'a", "'b"]]]])
]]));

const a = translate(
	["let", "id", ["lambda", "x", "x"],
		["let", "f",
			["lambda", 
				["x", ["forall", ["'a"], ["->", "'a", "'a"]]],
				["&", ["x", 1], ["x", null]]],
			["f", "id"]]]
);

console.log(util.inspect(a.inferSigma(env), {depth: null}));
