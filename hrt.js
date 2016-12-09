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
		return new ForAll(newBinders, this.zonk(env));
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
			return subsCheckRho(this, env, exp.check);
		} else {
			exp.infer.val = this.instantiate(env);
		}
	}
	/**
	 * @param{Environment} env
	 * @param{Type} that
	 */
	subsCheck(env, that) {
		const {map:skolTvs, rho2} = this.skolemise(env);
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
		return unify(this, that);
	}
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
		let {map: m1, type: t1} = skolemise(env, this.body.subst(m));
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
		return this.instantiate(env).subsCheckRho(that);
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
		let {map:m1, type:t1} = skolemise(env, this.arg);
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
		if (that instanceof Composite) {
			this.fn.subsCheck(that.fn);
			this.arg.subsCheckRho(that.arg);
			return true;
		} else {
			return unify(this, that);
		}
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
		if (this.typeRef.val) {
			let t1 = this.typeRef.val.zonk(env);
			this.typeRef.val = t1;
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
		return new Environment(this.uniqs, this.variables);
	}
	/**
	 * @param {string} name
	 * @returns {Type}
	 */
	lookup(name) {
		if (this.variables.has(name)) {
			return this.variables.get(name);
		} else {
			throw `Variable ${name} not found.`
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
		return expTy.quantify(env, Array.from(resMsvs));
	}
	/**
	 * @param{Environment} env
	 * @param{Type} sigma
	 */
	checkSigma(env, sigma) {
		const {map: mvs, type: rho} = sigma.skolemise(env);
		this.checkRho(rho);
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
	 * @param {number} n
	 */
	constructor(n) {
		super();
		this.lit = n;
	}
	isAtomic() {
		return true;
	}
	tcRho(env, exp) {
		return new Primitive("int").instSigma(env, exp);
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
		return ty.instSigma(exp);
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
		this.arg.checkRho(argTy);
		return resTy.instSigma(env, exp);
	}
}
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
			const env1 = env.extend(this.name, varTy);
			const bodyTy = this.body.inferRho(env1);
			exp.infer.val = FunctionType(varTy, bodyTy);
		}
	}
}
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
			const env1 = env.extend(this.name, this.type);
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
