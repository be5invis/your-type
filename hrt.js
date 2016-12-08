// //// TERMS
class Term {
	constructor() {}
	isAtomic() {
		return false;
	}
}
class Lit extends Term {
	constructor(n) {
		super();
		this.lit = n;
	}
	isAtomic() {
		return true;
	}
}
class Var extends Term {
	constructor(name) {
		super();
		this.name = name;
	}
	isAtomic() {
		return true;
	}
}
class App extends Term {
	constructor(fn, arg) {
		super();
		this.fn = fn;
		this.arg = arg;
	}
}
class Lam extends Term {
	constructor(param, body) {
		super();
		this.param = param;
		this.body = body;
	}
}
class ALam extends Term {
	constructor(param, type, body) {
		super();
		this.param = param;
		this.type = type;
		this.body = body;
	}
}
class Let extends Term {
	constructor(name, bind, body) {
		super();
		this.name = name;
		this.bind = bind;
		this.body = body;
	}
}
class Ann extends Term {
	constructor(type, body) {
		super();
		this.type = type;
		this.body = body;
	}
}

// //// TYPES
class Type {
	constructor() {}

	/**
	 * Get all meta type variables.
	 * @returns {Map<string, Type>}
	 */
	getMetaSlots() {
		let a = new Map;
		this._getMetaSlots(a);
		return a;
	}
	_getMetaSlots(a) {}
	// Get all free type variables.
	// a : Set String
	getFreeSlots() {
		let a = new Set;
		let bound = new Set;
		this._getFreeSlots(bound, a);
		return a;
	}
	_getFreeSlots(bound, a) {}
	// Get all binders of a type
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
	 * @returns {Type}
	 */
	skolemise(env) {
		return this;
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
/**
 * @param {Type} t
 * @returns {boolean}
 */
function badtype(t) {
	return t instanceof Slot && t.name[0] !== ".";
}
