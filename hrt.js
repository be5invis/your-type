// # `hrt.js`, A Rank-N Type Inferencer
// 本文主要参照 Simon Peyton Jones 等的论文 *Practical type inference for arbitrary-rank types* 实现了一个 Rank-N 的类型推理算法。
// 
// 此算法的逻辑学表述可参见文献 31 页，Haskell 代码可参见其附件。这份 JavaScript 代码由其 Haskell 版本改写而来。




const util = require("util");

// ## 第一部分，环境 $\Gamma$
// 我们使用「环境」来处理嵌套的作用域。每个环境包含两个部分：
// - uniqs：一个全局的计数器引用，产生临时变量时使用
// - variables：一个字符串到类型的映射，用来记录所有已经定型的变量名
class Environment {
	/**
	 * @param {{val:number}} uniqs
	 * @param {Map<string, Type>} variables
	 */
	constructor(uniqs, variables) {
		this.uniqs = uniqs;
		this.variables = variables;
	}
	// #### extend :: *this* Environment × string × Type → Environment
	// 创建一个扩展环境 $\Gamma, x:t$，增加一个变量
	/**
	 * @param {string} name
	 * @param {Type} type
	 */
	extend(name, type) {
		let v1 = new Map(this.variables);
		v1.set(name, type);
		return new Environment(this.uniqs, v1);
	}
	// #### extendN :: *this* Environment × [{name: string, type: Type}] → Environment
	// 创建一个扩展环境 $\Gamma,\overline{x:t}$，增加一组变量。此函数用于 let rec 的构建
	/**
	 * @param {{name: string, type: Type}[]} terms
	 */
	extendN(terms) {
		let v1 = new Map(this.variables);
		for (let {name, type} of terms) {
			v1.set(name, type);
		}
		return new Environment(this.uniqs, v1);
	}
	// #### lookup :: *this* Environment × string → Type
	// 查找名称定义
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
	// #### newUnique :: *this* Environment → number
	// 增加计数器，生成唯一性的数值
	newUnique() {
		this.uniqs.val += 1;
		return this.uniqs.val;
	}
	// #### newMetaSlotVal :: *this* Environment → MetaSlotVal
	// 生成新的 Meta slot value
	newMetaSlotVal() {
		const u = this.newUnique();
		const ref = { val: null };
		return new MetaSlotVal(u, ref);
	}
	// #### newSkolemVariable :: *this* Environment → string
	// 生成新的 Skolem slot 名称
	newSkolemVariable(s) {
		const u = this.newUnique();
		return rawNameToskolmeizedName(u, s);
	}
	// #### getTypes :: *this* Environment → IterableIterator Type
	// 获得所有已定义变量的类型列表
	getTypes() {
		return this.variables.values();
	}

	// #### getTypes :: *this* Environment → IterableIterator [number, MetaSlot]
	// 获得当前环境中所有已定义变量类型中的所有 Meta slot
	/**
	 * @param{IterableIterator<Type>} tys
	 */
	* getMetaSlotVars(tys) {
		for (let type of tys) {
			let type1 = type.zonk(this);
			yield* type1.getMetaSlots();
		}
	}
	// #### getTypes :: *this* Environment × → IterableIterator string
	// 获得当前环境中所有已定义变量类型中的所有自由 slot
	/**
	 * @param{IterableIterator<Type>} tys
	 */
	* getAllFreeSlots(tys) {
		for (let type of tys) {
			let type1 = type.zonk(this);
			yield* type1.getFreeSlots();
		}
	}
}

function rawNameToskolmeizedName(u, n) {
	return "." + u + "." + n;
}
function rawNameOfskolmeizedName(n) {
	return n.replace(/^\.\d+\./, "");
}


// ## 第二部分，类型
// 在我们的系统中，「类型」可以包含四种构造：
//
// * Slot，表示一个被量化的名称，使用符号 $a$ 表示。
// * Primitive，表示一个原始类型，如 $\rm int$。
// * Composite，表示一个复合类型，如 $\rm list\ int$。函数类型是一种二级复合。
// * ForAll，表示一个多态量化 $\forall \overline\alpha. t$。
// 
// 此外在推理过程中，会涉及一种 Meta Slot，它代表一个尚未完全决议的类型。使用这种方式处理推理中的中间结果最早可见于 Jones 的另一篇文献，*Boxy Types: Inference for Higher-Rank Types and Impredicativity*。
// 
// 我们将类型分为 $\sigma$, $\rho$, $\tau$ 三类，它们满足：
// * $\tau \rightarrow \mathrm{Primitive}\ |\  a\ |\ \tau_1 \tau_2$
// * $\rho \rightarrow \tau\ |\ \sigma_1 \sigma_2$
// * $\sigma \rightarrow \forall \overline{a}.\rho$
// 
// 可以看出，$\sigma$ 类型为直接包含多态的类型，$\rho$ 类型则为嵌有多态结构的复合类型。在传统的 Hindley-Milner 系统中，$\rho$ 类型的第二种形式并不允许，它和 $\tau$ 类型完全等价。
class Type {
	constructor() {}
	// #### inspect :: *this* Type → string
	inspect() {}
	// #### getMetaSlots :: *this* Type → Map number MetaSlot
	// 获取当前类型中所有出现的 Meta slot。返回一个 id 到 meta slot 的映射。根据 Meta slot value 的定义，任何两个 id 相同的 Meta slot 都视作相等。
	/**
	 * @returns {Map<number, MetaSlot>}
	 */
	getMetaSlots() {
		let a = new Map;
		this._getMetaSlots(a);
		return a;
	}
	_getMetaSlots(a) {}
	// #### getFreeSlots :: *this* Type → Set string
	// 获取当前类型中所有出现的未绑定 slot。返回它们的名字组成的集合。
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
	// #### getBinders :: *this* Type → Set string
	// 获取当前类型中所有被 forall 使用的 slot 名字。返回其集合。
	/**
	 * @returns{Set<string>}
	 */
	getBinders() {
		let a = new Set;
		this._getBinders(a);
		return a;
	}
	_getBinders() {}
	// #### subst :: *this* Type × Map string Type → Type
	// 根据 m 的要求，替换一些 slot 的内容。
	/**
	 * @param {Map<string, Type>} m
	 * @returns {Type}
	 */
	subst(m) {
		return this;
	}
	// #### instantiate :: *this* Type × Environment → Type
	// 在环境 env 中，实例化当前的多态类型。它会去除顶层的 $\forall$ 符号。
	/**
	 * @param {Environment} env
	 * @returns {Type}
	 */
	instantiate(env) {
		return this;
	}
	// #### skolmeize :: *this* Type × Environment → {map: Map string Slot, type: Type}
	// 在当前环境 env 中，产生当前类型的一个斯科伦范式形式。它可以看作实例化的递归版本，会展开每一层的多态，同时会返回新产生的临时变量的表（这里使用一个名字到 Slot 的 Map 实现）。我们不会展开复合类型的前件，避免错误地捕捉变量。此过程产生的类型必然保证：所有符合构造的后件不包含任何的多态。
	// 
	// 一个实例是：$\mathrm{skol}(\forall a.a\rightarrow(\forall b.b\rightarrow b))=\forall ab. a \rightarrow (b \rightarrow b)$
	/**
	 * @param {Environment} env
	 * @returns {{map: Map<string, Slot>, type: Type}}
	 */
	skolmeize(env) {
		return {
			map: new Map(),
			type: this
		};
	}
	// #### generalize :: *this* Type × Environment × [MetaSlotVal] → ForAll
	// 在当前环境 env 中，根据 mvs 列表泛化当前类型。将返回一个多态类型。
	/**
	 * @param {Environment} env
	 * @param {Array<MetaSlotVal>} mvs
	 * @returns {ForAll}
	 */
	generalize(env, mvs) {
		let usedBinders = this.getBinders();
		let nRef = { val: 0 };
		let newBinders = [];
		for (let slot of mvs) {
			let newBinder = new Slot(generateBinder(nRef, usedBinders));
			slot.typeRef.val = newBinder;
			newBinders.push(newBinder);
		}
		return new ForAll(newBinders.map(x => x.name), this.zonk(env));
	}
	// #### zonk :: *this* Type × Environment → Type
	// 消除掉当前类型中所有的 Meta Slot。
	/**
	 * @param {Environment} env
	 * @returns {Type}
	 */
	zonk(env) {
		return this;
	}
	// #### instSigmaInfer :: *this* Type × Environment → Type
	// 在类型推理时，生成一个实例化的版本
	//
	// INFER-INST: $\dfrac{}{\forall \overline a. \rho \le \sim [\overline{a\rightarrow\mathrm{fresh}}]\rho}$
	/**
	 * @param{Environment} env
	 * @returns{Type}
	 */
	instSigmaInfer(env) {
		return this.instantiate(env);
	}
	// #### instSigmaCheck :: *this* Type × Environment × Type → boolean
	// 在类型推理时，检查本类型是否符合需求
	/**
	 * @param{Environment} env
	 * @param{Type} expected
	 */
	instSigmaCheck(env, expected) {
		return this.subsCheckRho(env, expected);
	}
	// #### subsCheck :: *this* Type × Environment × Type → boolean <br> subsCheckRho :: *this* Type × Environment × Type → boolean
	// 判断某个类型是否比另一个类型更加「泛化」。
	// 我们把它拆分成两个部分：$\rm subsCheck$ 和 $\rm subsCheckRho$，前者处理两个 $\sigma$ 类型，后者处理一个 $\sigma$ 类型和一个 $\rho$ 类型。
	/**
	 * @param{Environment} env
	 * @param{Type} that
	 */
	subsCheck(env, that) {
		// $\sigma_1 \le \sigma_2$ 成立，当且仅当：
		const {map: skolTvs, type: rho2} = that.skolmeize(env);
		//  - $\sigma_1 \le \rho, \forall \overline a. \rho = \mathrm{skol}(\sigma_2)$
		this.subsCheckRho(env, rho2);
		//  - 并且，$\sigma_1$ 的自由变量中，$\sigma_2$ 中的对应者没有被「提出来」
		//    
		//    $\overline a \not\in \mathrm{free}(\sigma_1)$
		const escTvs = new Set(env.getAllFreeSlots([this]));
		for (let [k, v] of skolTvs) {
			if (escTvs.has(rawNameOfskolmeizedName(k))) {
				throw "Subsumption check failed"
			}
		}
	}
	// ${\rm subsCheckRho}(\sigma, \rho)$ 将会检查是否 $\sigma$ 比 $\rho$ 更加泛化（$\sigma\le\rho$）。
	/**
	 * @param{Environment} env
	 * @param{Type} that
	 */
	subsCheckRho(env, that) {
		if (that instanceof Composite) {
			const [f1, a1] = unifyComposite(this, env);
			return subsCheckComposite(env, that.contravariant, f1, that.fn, a1, that.arg);
		} else {
			return unify(this, that);
		}
	}
}

// #### subsCheckComposite :: Environment × boolean × Type × Type × Type × Type → boolean
// 复合类型的小前提检查，注意反变性。在这里我们限制任何复合类型的构造器部分是**非变**的，这样可以降低复杂性。对于协/反变性的更精细处理可以递归展开 f1/f2 的部分，然后分别处理每个参数。
function subsCheckComposite(env, contravariant, f1, f2, a1, a2) {
	f1.subsCheck(env, f2);
	if (contravariant) {
		a2.subsCheck(env, a1);
	} else {
		a1.subsCheckRho(env, a2);
	}
}

// #### generateBinder :: ref number × Set string → string
// 获取新的名字，用于泛化过程中的重命名
function generateBinder(nRef, used) {
	nRef.val += 1;
	let name = "t" + nRef.val;
	while (used.has(name)) {
		nRef.val += 1;
		name = "t" + nRef.val;
	}
	return name;
}

// ### 基本类型
class Primitive extends Type {
	/**
	 * @param {string} name
	 */
	constructor(name) {
		super();
		this.name = name;
	}
	inspect() {
		return this.name;
	}
}
// ### 限制的类型变量，$a$
// Slot 可能有两种来源：
//
// - 在外面某个 $\forall$ 之后出现
// - 由斯科伦化产生
//
// 我们使用名字区分之，名称以 `.` 开头的都是由斯科伦化产生产生的 Slot
class Slot extends Type {
	/**
	 * @param {string} name
	 */
	constructor(name) {
		super();
		this.name = name;
	}
	inspect() {
		return "'" + this.name;
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
	isSkolem() {
		return this.name[0] === ".";
	}
	equalTo(that) {
		if (this.isSkolem() && that.isSkolem()) {
			return rawNameOfskolmeizedName(this.name) === rawNameOfskolmeizedName(that.name);
		} else if (!this.isSkolem() && !that.isSkolem()) {
			return this.name === that.name;
		} else {
			return false;
		}
	}
}
// ### 复合类型，$\sigma_1 \sigma_2$
class Composite extends Type {
	// 复合类型由三个部分构成：
	// - 构造器部分，*fn*
	// - 参数部分，*arg*
	// - 协变/反变性，*contravariant*
	/**
	 * @param {Type} fn
	 * @param {Type} arg
	 * @param {boolean} contravariant
	 */
	constructor(fn, arg, contravariant) {
		super();
		this.fn = fn;
		this.arg = arg;
		this.contravariant = contravariant || false;
	}
	inspect() {
		if (this.fn instanceof Composite && this.fn.fn instanceof Primitive && !/^\w/.test(this.fn.fn.name)) {
			const left = this.fn.arg;
			const op = this.fn.fn;
			if (left instanceof Primitive || left instanceof Slot) {
				return left.inspect() + " " + op.name + " " + this.arg.inspect();
			} else {
				return "(" + left.inspect() + ") " + op.name + " " + this.arg.inspect();
			}
		} else {
			if (this.arg instanceof Primitive || this.arg instanceof Slot) {
				return this.fn.inspect() + " " + this.arg.inspect();
			} else {
				return this.fn.inspect() + " (" + this.arg.inspect() + ")";
			}
		}
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
		return new Composite(this.fn.subst(m), this.arg.subst(m), this.contravariant);
	}
	// 复合类型的斯科伦化需要小心地处理其参数部分：
	skolmeize(env) {
		let {map: m1, type: t1} = this.fn.skolmeize(env);
		if (this.contravariant) {
			//   - 如果这个类型是反变的，保留其 arg 部分；
			return {
				map: m1,
				type: new Composite(t1, this.arg, this.contravariant)
			};
		} else {
			//   - 如果这个类型是协变的，展开其 arg 部分。
			let {map: m2, type: t2} = this.arg.skolmeize(env);
			for (let [k, v] of m1.entries()) {
				m2.set(k, v);
			}
			return {
				map: m2,
				type: new Composite(t1, t2, this.contravariant)
			};
		}
	}
	zonk(env) {
		return new Composite(this.fn.zonk(env), this.arg.zonk(env), this.contravariant);
	}
	/**
	 * @param{Environment} env
	 * @param{Type} that
	 */
	subsCheckRho(env, that) {
		const [f2, a2] = unifyComposite(that, env);
		return subsCheckComposite(env, this.contravariant, this.fn, f2, this.arg, a2);
	}
}

// ### 多态类型，$\forall \overline a. \rho$
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
	inspect() {
		if (this.quantifiers.length) {
			return "forall " + this.quantifiers.join(" ") + ". " + this.body.inspect();
		} else {
			return this.body.inspect();
		}
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
	// 多态类型进行替换的时候，需要从映射 m 中删掉其量化子 $\overline a$ 包含的项目。
	subst(m) {
		let m1 = new Map(m);
		for (let q of this.quantifiers) {
			m1.delete(q);
		}
		return new ForAll(this.quantifiers, this.body.subst(m1));
	}
	// 实例化时，创建一个量化子 $\overline a$ 到「新变量」的映射，然后返回其内容经过替换时的结果。
	instantiate(env) {
		let m = new Map();
		for (let q of this.quantifiers) {
			m.set(q, new MetaSlot(env.newMetaSlotVal()));
		}
		return this.body.subst(m);
	}
	// 多态类型的深斯科伦化会合并内外两层的变量表。
	/**
	 * @param {Environment} env
	 */
	skolmeize(env) {
		let m = new Map();
		let mSub = new Map();
		for (let q of this.quantifiers) {
			const sv = env.newSkolemVariable(q);
			const ss = new Slot(sv);
			m.set(sv, ss);
			mSub.set(q, ss);
		}
		let {map: m1, type: t1} = this.body.subst(mSub).skolmeize(env);
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

// ### Meta Slot，推理过程中的未决议类型
class MetaSlot extends Type {
	/**
	 * @param {MetaSlotVal} arg - Argument
	 */
	constructor(arg) {
		super();
		this.arg = arg;
	}
	inspect() {
		return "?" + this.arg.id;
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
// ### MetaSlotVal: MetaSlot 的值
// MetaSlotVal 包含两个字段，编号 id 和 typeRef，一个对类型的引用。两个 MetaSlotVal 的 id 相同即视为相等。
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


// ## 第三部分，合一


// ### unify :: type × type → boolean
// 尝试合一两个类型，成功返回 true，否则报错。
/**
 * @param {Type} t1
 * @param {Type} t2
 * @returns {boolean}
 */
function unify(t1, t2) {
	if (badtype(t1) || badtype(t2)) throw "Should not be here."
	if (t1 instanceof Slot && t2 instanceof Slot && t1.equalTo(t2)) return true;
	if (t1 instanceof MetaSlot && t2 instanceof MetaSlot && t1.arg.equalTo(t2.arg)) return true;
	if (t1 instanceof MetaSlot) return unifyMetaSlot(t1.arg, t2);
	if (t2 instanceof MetaSlot) return unifyMetaSlot(t2.arg, t1);
	if (t1 instanceof Composite && t2 instanceof Composite) {
		unify(t1.fn, t2.fn);
		unify(t2.arg, t2.arg);
		return true;
	}
	if (t1 instanceof Primitive && t2 instanceof Primitive && t1.name === t2.name) { return true; }
	throw new Error(`Cannot unify ${t1.inspect()} with ${t2.inspect()}`)
}
/**
 * @param {Type} t
 * @returns {boolean}
 */
function badtype(t) {
	return t instanceof Slot && !t.isSkolem();
}
// ### unifyMetaSlot :: MetaSlotVal × Type → boolean
// Meta slot 的合一，一般情况
/**
 * @param {MetaSlotVal} msv
 * @param {Type} ty
 */
function unifyMetaSlot(msv, ty) {
	if (msv.typeRef.val) {
		return unify(msv.typeRef.val, ty);
	} else {
		return unifyUnbound(msv, ty);
	}
}
// ### unifyUnbound :: MetaSlotVal × Type → boolean
// Meta slot 的合一，未绑定情况
/**
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

// ### unifyFun :: Type × Environment → boolean
// 合一类型到函数
/**
 * @param {Type} type
 * @param {Environment} env
 * @returns {[Type, Type]}
 */
function unifyFun(type, env) {
	if (type instanceof Composite
		&& type.fn instanceof Composite
		&& type.fn.fn instanceof Primitive
		&& type.fn.fn.name === "->") {
		return [type.fn.arg, type.arg];
	} else {
		const argMs = new MetaSlot(env.newMetaSlotVal());
		const resMs = new MetaSlot(env.newMetaSlotVal());
		unify(FunctionType(argMs, resMs), type);
		return [argMs, resMs];
	}
}

// ### FunctionType :: Type × Type → Type
// 构造一个函数类型
function FunctionType(arg, body) {
	return new Composite(new Composite(new Primitive("->"), arg, true), body, false);
}

// ### unifyComposite :: Type × Environment → boolean
// 合一类型到任意复合类型
/**
 * @param {Type} type
 * @param {Environment} env
 * @returns {[Type, Type]}
 */
function unifyComposite(type, env) {
	if (type instanceof Composite) {
		return [type.fn, type.arg];
	} else {
		const argMs = new MetaSlot(env.newMetaSlotVal());
		const resMs = new MetaSlot(env.newMetaSlotVal());
		unify(new Composite(argMs, resMs), type);
		return [argMs, resMs];
	}
}





// ## 第四部分，主推理算法
// 由于高阶类型的介入，Damas-Hindley-Milner 系统中的单一「推理」方法需要拆分为一对方法，`infer` 和 `check`；它们会再根据所处理的类型（$\sigma$ 或者 $\rho$ 类型），再各自进行拆分，因此最终得到四个方法：`inferRho`, `checkRho`, `inferSigma`, `checkSigma`。
class Term {
	constructor() {}
	isAtomic() {
		return false;
	}
	// #### checkRho :: *this* Term × Environment × Type → boolean
	// 在环境 env 中检查当前表达式是否符合 $\rho$ 类型 type
	//
	// $\Gamma\vdash t : \rho$
	/**
	 * @param {Environment} env
	 * @param {Type} type
	 */
	_checkRho(env, type) {}
	checkRho(env, type) {
		return this._checkRho(env, type);
	}
	// #### inferRho :: *this* Term × Environment → Type
	// 在环境 env 中推理，尝试得到 $\rho$ 类型（或者报错）
	//
	// $\Gamma\vdash t :\sim \rho$
	/**
	 * @param {Environment} env
	 * @returns {Type}
	 */
	_inferRho(env) {}
	inferRho(env) {
		const t = this._inferRho(env);
		if (!t) throw "Cannot decide type"
		return t;
	}

	// #### checkSigma :: *this* Term × Environment × Type → boolean
	// 在环境 env 中检查当前表达式是否符合 $\sigma$ 类型 type
	//
	// CHECK-SIGMA: $\dfrac{\overline a \not\in \mathrm{free}(\Gamma)\quad \Gamma\vdash t:\rho\quad \forall\overline a.\rho = \mathrm{skol}(\sigma)}{\Gamma\vdash^* t:\sigma}$
	/**
	 * @param{Environment} env
	 * @param{Type} sigma
	 */
	checkSigma(env, type) {
		const {map: mvs, type: rho} = type.skolmeize(env);
		this.checkRho(env, rho);
		const envTys = env.getTypes();
		const escTvs = new Set(env.getAllFreeSlots(envTys));
		for (let [name, slot] of mvs) {
			if (escTvs.has(rawNameOfskolmeizedName(name))) {
				throw "Type is not polymorphic enough"
			}
		}
		return true;
	}

	// #### inferSigma :: *this* Term × Environment → Type
	// 在环境 env 中推理，尝试得到 $\sigma$ 类型（或者报错）
	//
	// INFER-SIGMA: $\dfrac{\overline a = \mathrm{free}(\rho)-\mathrm{free}(\Gamma)\quad \Gamma\vdash t:\sim \rho}{\Gamma\vdash^* t:\sim\forall\overline a.\rho}$
	/**
	 * @param{Environment} env
	 * @returns{Type}
	 */
	inferSigma(env) {
		const expTy = this.inferRho(env);
		const envTys = env.getTypes();
		const envMsvs = env.getMetaSlotVars(envTys);
		const resMsvs = new Map(env.getMetaSlotVars([expTy]));
		for (let [id, v] of envMsvs) {
			resMsvs.delete(id);
		}
		return expTy.generalize(env, Array.from(resMsvs.values()));
	}
}
// ### 直接量
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
	// CHECK-LIT: $\dfrac{}{\Gamma\vdash \iota:\mathrm{literalTypeOf}(\iota)}$
	_checkRho(env, exp) {
		if (typeof this.lit === "number") {
			return new Primitive("int").instSigmaCheck(env, exp);
		} else if (typeof this.lit === "string") {
			return new Primitive("str").instSigmaCheck(env, exp);
		} else if (typeof this.lit === "boolean") {
			return new Primitive("boolean").instSigmaCheck(env, exp);
		} else {
			return new Primitive("unit").instSigmaCheck(env, exp);
		}
	}
	// INFER-LIT: $\dfrac{}{\Gamma\vdash \iota:\sim\mathrm{literalTypeOf}(\iota)}$
	_inferRho(env) {
		if (typeof this.lit === "number") {
			return new Primitive("int").instSigmaInfer(env);
		} else if (typeof this.lit === "string") {
			return new Primitive("str").instSigmaInfer(env);
		} else if (typeof this.lit === "boolean") {
			return new Primitive("boolean").instSigmaInfer(env);
		} else {
			return new Primitive("unit").instSigmaInfer(env);
		}
	}
}
// ### 变量
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
	// CHECK-VAR: $\dfrac{\sigma\le\rho}{\Gamma, x:\sigma\vdash x:\rho}$
	_checkRho(env, expected) {
		return env.lookup(this.name).instSigmaCheck(env, expected);
	}
	// INFER-VAR: $\dfrac{\sigma\le\sim\rho}{\Gamma, x:\sigma\vdash x:\sim\rho}$
	_inferRho(env) {
		return env.lookup(this.name).instSigmaInfer(env);
	}
}
// ### 函数调用
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
	// CHECK-APP: $\dfrac{\Gamma\vdash t:\sim(\sigma \rightarrow \sigma')\quad \Gamma\vdash^*u:\sigma\quad \sigma'\le\rho'}{\Gamma\vdash t\ u : \rho}$
	_checkRho(env, expected) {
		const funTy = this.fn.inferRho(env);
		const [argTy, resTy] = unifyFun(funTy, env);
		this.arg.checkSigma(env, argTy);
		return resTy.instSigmaCheck(env, expected);
	}
	// INFER-APP: $\dfrac{\Gamma\vdash t:\sim(\sigma \rightarrow \sigma')\quad\Gamma\vdash^* u:\sigma\quad \sigma'\le\sim\rho'}{\Gamma\vdash t\ u :\sim \rho}$
	_inferRho(env) {
		const funTy = this.fn.inferRho(env);
		const [argTy, resTy] = unifyFun(funTy, env);
		this.arg.checkSigma(env, argTy);
		return resTy.instSigmaInfer(env);
	}
}
// ### 函数抽象
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
	// CHECK-LAM: $\dfrac{\Gamma, x:\sigma_x\vdash^* t:\sigma_t}{\Gamma\vdash(\lambda\ x.t):\sigma_x\rightarrow\sigma_t}$
	/**
	 * @param{Environment} env
	 * @param{Type} expected
	 */
	_checkRho(env, expected) {
		const [varTy, bodyTy] = unifyFun(expected, env);
		const env1 = env.extend(this.param, varTy);
		return this.body.checkRho(env1, bodyTy); // bodyTy is always a Rho-type.
	}
	// INFER-LAM: $\dfrac{\Gamma, x:\tau\vdash t:\sim\rho}{\Gamma\vdash(\lambda\ x.t):\sim\tau\rightarrow\rho}$
	/**
	 * @param{Environment} env
	 * @returns{Type} 
	 */
	_inferRho(env) {
		const varTy = new MetaSlot(env.newMetaSlotVal());
		const env1 = env.extend(this.param, varTy);
		const bodyTy = this.body.inferRho(env1);
		return FunctionType(varTy, bodyTy);
	}
}
// ### 标记了参数类型的函数抽象
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
	// CHECK-ALAM: $\dfrac{\sigma_a\le\sigma_x\quad\Gamma, x:\sigma_x\vdash^* t:\sigma_t}{\Gamma\vdash(\lambda(x:\sigma_x).t):\sigma_a\rightarrow\sigma_t}$
	/**
	 * @param{Environment} env
	 * @param{Type} expected
	 */
	_checkRho(env, expected) {
		const [varTy, bodyTy] = unifyFun(expected, env);
		varTy.subsCheck(this.type);
		const env1 = env.extend(this.param, varTy);
		return this.body.checkRho(env1, bodyTy);
	}
	// INFER-ALAM: $\dfrac{\Gamma, x:\sigma\vdash t:\sim\rho}{\Gamma\vdash(\lambda(x:\sigma).t):\sim\sigma\rightarrow\rho}$
	/**
	 * @param{Environment} env
	 * @returns{Type} 
	 */
	_inferRho(env) {
		const env1 = env.extend(this.param, this.type);
		const bodyTy = this.body.inferRho(env1);
		return FunctionType(this.type, bodyTy);
	}
}
// ### 非递归 Let 绑定
class Let extends Term {
	/**
	 * @param {Array<{name: string, bind: Term}>} terms
	 * @param {Term} body
	 */
	constructor(terms, body) {
		super();
		this.terms = terms;
		this.body = body;
	}
	// CHECK-LET: $\dfrac{\Gamma\vdash^* t: \sigma'\quad \Gamma, x:\sigma'\vdash u:\rho}{\Gamma\vdash(\mathbf{let}\ (x=t).u):\rho}$
	/**
	 * @param{Environment} env
	 * @param{Type} expected
	 */
	_checkRho(env, expected) {
		const varTys = this.terms.map(({name, bind}) => ({name, type: bind.inferSigma(env)}));
		const env1 = env.extendN(varTys);
		return this.body.checkRho(env1, expected);
	}
	// INFER-LET: $\dfrac{\Gamma\vdash^* t:\sim \sigma'\quad \Gamma, x:\sigma'\vdash u:\sim\rho}{\Gamma\vdash(\mathbf{let}\ (x=t).u):\sim\rho}$
	/**
	 * @param{Environment} env
	 * @returns{Type} 
	 */
	_inferRho(env) {
		const varTys = this.terms.map(({name, bind}) => ({name, type: bind.inferSigma(env)}));
		const env1 = env.extendN(varTys);
		return this.body.inferRho(env1);
	}
}
// ### 递归 Let 绑定
class LetRec extends Term {
	/**
	 * @param {Array<{name: string, bind: Term, type: Type?}>} terms
	 * @param {Term} body
	 */
	constructor(terms, body) {
		super();
		this.terms = terms;
		this.body = body;
	}
	// CHECK-LETREC1: $\dfrac{\Gamma, x:\mathrm{fresh}\vdash^* t: \sigma'\quad \Gamma, x:\sigma'\vdash u:\rho}{\Gamma\vdash(\mathbf{let\ rec}\ (x=t).u):\rho}$
	// 
	// CHECK-LETREC2: $\dfrac{\Gamma, x:\sigma\vdash^* t: \sigma'\quad \Gamma, x:\sigma'\vdash u:\rho}{\Gamma\vdash(\mathbf{let\ rec}\ (x:\sigma=t).u):\rho}$
	/**
	 * @param{Environment} env
	 * @param{Type} expected
	 */
	_checkRho(env, expected) {
		const env1TypeBindings = this.terms.map(({name, type}) => ({
			name,
			type: type || new MetaSlot(env.newMetaSlotVal())
		}));
		const env1 = env.extendN(env1TypeBindings);
		const varTys = this.terms.map(({name, bind}) => ({name, type: bind.inferSigma(env1)}));
		const env2 = env.extendN(varTys);
		return this.body.checkRho(env2, expected);
	}
	// INFER-LETREC1: $\dfrac{\Gamma, x:\mathrm{fresh}\vdash^* t:\sim \sigma'\quad \Gamma, x:\sigma'\vdash u:\sim\rho}{\Gamma\vdash(\mathbf{let\ rec}\ (x=t).u):\sim\rho}$
	//
	// INFER-LETREC2: $\dfrac{\Gamma, x:\sigma\vdash^* t:\sim \sigma'\quad \Gamma, x:\sigma'\vdash u:\sim\rho}{\Gamma\vdash(\mathbf{let\ rec}\ (x:\sigma=t).u):\sim\rho}$
	/**
	 * @param{Environment} env
	 * @returns{Type} 
	 */
	_inferRho(env) {
		const env1TypeBindings = this.terms.map(({name, type}) => ({
			name,
			type: type || new MetaSlot(env.newMetaSlotVal())
		}));
		const env1 = env.extendN(env1TypeBindings);
		const varTys = this.terms.map(({name, bind, type}) => {
			const inferredType = bind.inferSigma(env1);
			if (type) {
				type.subsCheck(env, inferredType);
			}
			return {name, type: inferredType};
		});
		const env2 = env.extendN(varTys);
		return this.body.inferRho(env2);
	}
}
// ### 显式窄化
class Ann extends Term {
	/**
	 * @param {Type} type
	 * @param {Term} body
	 */
	constructor(body, type) {
		super();
		this.type = type;
		this.body = body;
	}
	// CHECK-ANN: $\dfrac{\Gamma\vdash^* t:\sigma \quad \sigma\le\rho}{\Gamma\vdash(t:\sigma):\rho}$
	/**
	 * @param{Environment} env
	 * @param{Type} expected
	 */
	_checkRho(env, expected) {
		this.body.checkSigma(env, this.type);
		return this.type.instSigmaCheck(env, expected);
	}
	// INFER-ANN: $\dfrac{\Gamma\vdash^* t:\sigma \quad \sigma\le\sim\rho}{\Gamma\vdash(t:\sigma):\sim\rho}$
	/**
	 * @param{Environment} env
	 * @returns{Type}
	 */
	_inferRho(env) {
		this.body.checkSigma(env, this.type);
		return this.type.instSigmaInfer(env);
	}
}

// ## 测试部分
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
			return new Composite(translateType(a[0]), translateType(a[1]), a[0] === "->" ? true : false);
		} else {
			const fnpart = translateType(a.slice(0, -1));
			const argpart = translateType(a[a.length - 1]);
			return new Composite(fnpart, argpart, false);
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
			return new Let(
				a.slice(1, -1).map(form => ({name: form[0], bind: translate(form[1])})),
				translate(a[a.length - 1]));
		} else if (a[0] === "letrec") {
			return new LetRec(
				a.slice(1, -1).map(form => ({name: form[0], bind: translate(form[1]), type: form[2] ? translateType(form[2]) : null})),
				translate(a[a.length - 1]));
		} else if (a[0] === "lambda" && a.length >= 3) {
			const fn0 = translate(a[a.length - 1]);
			return a.slice(1, -1).reduceRight((fn, term) => (typeof term === "string")
				? new Lam(term, fn)
				: new ALam(term[0], translateType(term[1]), fn), fn0);
		} else if (a[0] === "begin") {
			return translate(a.slice(1).reduceRight((y, x) => ["seq", x, y]));
		} else if (a[0] === "::") {
			return new Ann(translate(a[1]), translateType(a[2]));
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

const env = new Environment({ val: 0 }, new Map([
	["&", translateType(["forall", ["'a", "'b"],
		["->", "'a",
			["->", "'b",
				["*", "'a", "'b"]]]])],
	["+", translateType(["->", "int", ["->", "int", "int"]])],
	["-", translateType(["->", "int", ["->", "int", "int"]])],
	["empty?", translateType(["forall", ["'a"], ["->", ["list", '"a'], "bool"]])],
	["zero?", translateType(["->", "int", "bool"])],
	["cdr", translateType(["forall", ["'a"], ["->", ["list", '"a'], ["list", "'a"]]])],
	["if", translateType(["forall", ["'a"], ["->",
		"bool",
		["->", "'a", ["->", "'a", "'a"]]]])],
	["somelist", translateType(["list", "int"])],
	["box", translateType(["forall", ["'t"], ["->", "'t", ["forall", ["'a"], ["box", "'a"]]]])],
	["unbox", translateType(["forall", ["'t"], ["->", ["forall", ["'a"], ["box", "'a"]], "'t"]])]
]));

const a = translate(
	["letrec",
		["even?", ["lambda", ["x", "int"],
			["if", ["zero?", "x"],
				true,
				["odd?", ["-", "x", 1]]]]],
		["odd?", ["lambda", ["x", "int"],
			["if", ["zero?", "x"],
				false,
				["even?", ["-", "x", 1]]]]],
		["id", ["lambda", "x", "x"]],
		["id_dyn",
			["lambda", ["x", ["forall", ["'a"], ["box", "'a"]]], ["::", ["unbox", "x"], "int"]],
			["->", ["forall", ["'a"], ["box", "'a"]], "int"]],
		["let",
			["strange",
				["lambda",
					["f", ["forall", ["'a"], ["->", "'a", "'a"]]],
					["&", ["f", 1], ["f", ["even?", 5]]]]],
			["&", ["strange", "id"], ["id_dyn", ["box", 1]]]]]
);

// 应当返回：`(int * boolean) * int`
console.log(util.inspect(a.inferSigma(env).zonk(env), { depth: null }));
