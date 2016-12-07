require("colors");

// A monomorphic type
class Monomorphic {
	constructor() {}
	inspect() {} // Pretty print type
	getMangler() {} // Get a name for mangler
	applySub(m) {} // Apply a substitution m
	equalTo(t) { // Equality
		return false;
	}
	getFreeSlots(m, a) {} // Get all free slots
	freeFrom(s) {} // type t is free freom slot s
	isClosed() {
		return false;
	}
}
// Slots for free variables
class Slot extends Monomorphic {
	constructor(name) {
		super();
		this.name = name;
	}
	inspect() {
		return ("'" + this.name).blue.bold + "".reset;
	}
	getMangler() {
		return ("'" + this.name);
	}
	applySub(m) {
		const r = m.get(this);
		if (!r || r === this) return this;
		return r.applySub(m);
	}
	equalTo(t) {
		return t && t instanceof Slot && this.name === t.name;
	}
	getFreeSlots(m, a) {
		if (!m.has(this) && !a.has(this)) a.add(this);
	}
	freeFrom(s) {
		return this !== s;
	}
	isClosed() {
		return false;
	}
}
// Primitive types
class Primitive extends Monomorphic {
	constructor(name, kind) {
		super();
		this.name = name;
	}
	inspect() {
		return this.name.yellow + "".reset;
	}
	getMangler() {
		return this.name;
	}
	applySub(m) {
		return this;
	}
	equalTo(t) {
		return t && t instanceof Primitive && this.name === t.name;
	}
	freeFrom(s) {
		return true;
	}
	isClosed() {
		return true;
	}
}
// Composite types, like [(->) a b] or [List a]
class Composite extends Monomorphic {
	constructor(ctor, argument) {
		super();
		this.ctor = ctor;
		this.argument = argument;
	}
	inspect() {
		if (this.ctor instanceof Composite && this.ctor.ctor instanceof Primitive && this.ctor.ctor.name === "->") {
			const left = this.ctor.argument;
			const right = this.argument;
			if (left instanceof Composite) {
				return "(" + left.inspect() + ")" + (" -> ".cyan.bold + "".reset) + right.inspect();
			} else {
				return left.inspect() + (" -> ".cyan.bold + "".reset) + right.inspect();
			}
		}
		if (this.argument instanceof Composite) {
			return this.ctor.inspect() + " (" + this.argument.inspect() + ")";
		} else {
			return this.ctor.inspect() + " " + this.argument.inspect() + "";
		}
	}
	getMangler() {
		if (this.argument instanceof Composite) {
			return this.ctor.getMangler() + " (" + this.argument.getMangler() + ")";
		} else {
			return this.ctor.getMangler() + " " + this.argument.getMangler() + "";
		}
	}
	applySub(m) {
		return new Composite(this.ctor.applySub(m), this.argument.applySub(m));
	}
	equalTo(t) {
		return t && t instanceof Composite && this.ctor.equalTo(t.ctor) && this.argument.equalTo(t.argument);
	}
	getFreeSlots(m, a) {
		this.ctor.getFreeSlots(m, a);
		this.argument.getFreeSlots(m, a);
	}
	freeFrom(s) {
		return this.ctor.freeFrom(s) && this.argument.freeFrom(s);
	}
	isClosed() {
		return this.ctor.isClosed() && this.argument.isClosed();
	}
}

function convertToNumberingScheme(number) {
	let baseChar = ("a").charCodeAt(0);
	let letters = "";

	do {
		number -= 1;
		letters = String.fromCharCode(baseChar + (number % 26)) + letters;
		number = (number / 26) >> 0;
	} while (number > 0);

	return letters;
}


class Polymorphic {
	constructor(quantifier, base) {
		this.quantifier = quantifier;
		this.base = base;
	}
	inspect() {
		let buf = "forall".red.bold;
		for (let item of this.quantifier) {
			buf += " " + item.inspect();
		}
		return buf + ". " + this.base.inspect();
	}
	instance(gen) {
		let m = new Map();
		for (let key of this.quantifier) {
			m.set(key, gen());
		}
		return {
			type: this.base.applySub(m),
			variables: m
		};
	}
	applySub(m) {
		return new Polymorphic(this.quantifier, this.base.applySub(m));
	}
}

// Unify two monomorphic types, p and q with slot mapping m.
function unify(m, s, t) {
	if (s instanceof Slot && t instanceof Slot && s.applySub(m).equalTo(t.applySub(m))) {
		return true;
	} else if (s instanceof Primitive && t instanceof Primitive && s.name === t.name && s.kind === t.kind) {
		return true;
	} else if (s instanceof Composite && t instanceof Composite) {
		return unify(m, s.ctor, t.ctor) && unify(m, s.argument, t.argument);
	} else if (s instanceof Slot) {
		let t1 = t.applySub(m);
		if (t1.freeFrom(s)) {
			m.set(s, t1);
			return true;
		} else {
			return false;
		}
	} else if (t instanceof Slot) {
		let s1 = s.applySub(m);
		if (s1.freeFrom(t)) {
			m.set(t, s1);
			return true;
		} else {
			return false;
		}
	} else {
		return false;
	}
}

// Slot symbol table
let st = {};
function slot(name) {
	if (st[name])return st[name];
	const t = new Slot(name);
	st[name] = t;
	return t;
}
// Primitive symbol table
let pt = {};
function prim(name, kind) {
	if (pt[name])return pt[name];
	const t = new Primitive(name, kind);
	pt[name] = t;
	return t;
}
// Composite types
function cmpt(ctor, argument) {
	const t = new Composite(ctor, argument);
	return t;
}
function arrow(p, q) {
	return cmpt(cmpt(prim("->"), p), q);
}
function product(p, q) {
	return cmpt(cmpt(prim("*"), p), q);
}

exports.Monomorphic = Monomorphic;
exports.Polymorphic = Polymorphic;
exports.Slot = Slot;
exports.Primitive = Primitive;
exports.Composite = Composite;
exports.unify = unify;

exports.slot = slot;
exports.prim = prim;
exports.cmpt = cmpt;
exports.arrow = arrow;
