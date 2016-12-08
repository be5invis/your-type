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
	// Get all meta type variables.
	// a : Map id MetaTv
	// default: pass
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
	// Substitute type variables to a corresponded type.
	// m : Map String Type
	subst(m) {
		return this;
	}
}
class ForAll extends Type {
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
}
class Primitive extends Type {
	constructor(name) {
		super();
		this.name = name;
	}
}
class Slot extends Type {
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
}
class MetaSlot extends Type {
	constructor(arg) {
		super();
		this.arg = arg;
	}
	_getMetaSlots(a) {
		if (!a.has(this.arg.id)) {
			a.set(this.arg.id, this.arg);
		}
	}
}
// MetaVal -- can unify with any tau-type
class MetaSlotVal {
	constructor(id, tau) {
		this.id = id;
		this.tau = tau;
	}
	equalTo(that) {
		return that && that instanceof MetaSlotVal && that.id === this.id;
	}
}

// //// Environments
class Environment {
	constructor(uniqs, variables) {
		this.uniqs = uniqs;
		this.variables = variables;
	}
	extend(name, type) {
		let v1 = new Map(this.variables);
		v1.set(name, type);
		return new Environment(this.uniqs, this.variables);
	}
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


function instantiate(env, type) {
	if (type instanceof ForAll) {
		let m = new Map();
		for (let q of type.quantifiers) {
			m.set(q, new MetaSlot(env.newMetaSlotVal()));
		}
		return type.body.subst(m);
	} else {
		return type;
	}
}

function skolemise(env, type) {
}
