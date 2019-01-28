// -- Grit: grammar support module ------------------------------------------------

/*	The MIT License (MIT)
 *
 *	Copyright (c) 2015,2016,2017,2018 Peter Cashin
 *
 *	Permission is hereby granted, free of charge, to any person obtaining a copy
 *	of this software and associated documentation files (the "Software"), to deal
 *	in the Software without restriction, including without limitation the rights
 *	to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 *	copies of the Software, and to permit persons to whom the Software is
 *	furnished to do so, subject to the following conditions:
 *
 *	The above copyright notice and this permission notice shall be included in all
 *	copies or substantial portions of the Software.
 *
 *	THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 *	IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 *	FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 *	AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 *	LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 *	OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 *	SOFTWARE.
 */

;(function() { // name-space wrapper -- expose Grit at the bottom of this file...

	/*
	 Grit() usage:

	 Using JavaScript ES6 ... tag template rules ............................

		var myGrit = Grit` ... rules ... `;

		myGrit.parse("input..")

	 Using JavaScript ES5 ...................................................

		var myGrit = Grit("rule0..", "rule1", ...); // a new Grit grammar
		var myGrit = new Grit("rule0..", "rule1..", ...); // same thing

		myGrit.parse("input..")

	 Action functions (semantic actions) ....................................

		rule := .....  :: foo
		rule :~ .....  :: foo

		myGrit.foo = function(...) { ... } // define a "foo" action function

		Use $ to trace parser actions:

		rule := or :~ .....  :: $foo

	 Note:

	 * action function names must not conflict with the reserved names:
	 	parse, trace, _privateNames...

	 * The 'this' context for actions is an instance of a Parser object:
	 	input = the input string being parsed
	 	pos   = current parser position
	 	grit  = the grammar rules

		this.prototype = other Grit functions...

	 */

	var FAIL = null; // return value for failure

	var Grit = function() { // call may be ES5 or ES6, but Grit itself does not require ES6
		var grit = this; // may be called as: Grit() or new Grit()
		if (!(this instanceof Grit)) { grit = new Grit(); }
		grit._define.apply(grit, arguments); // i.e. ...arguments, but avoids using ES6 in Grit
		return grit;
	}

// -- grip -- Grit prototype ------------------------------------------------

	Grit.prototype = {};

	var grip = Grit.prototype;

	var RULE = /^\s*(\w+)\s*([:][=~:])\s*([^\n\r]*)/;

	var PEG_RULE = ':=', REGEXP_RULE = ':~', FUN_RULE = '::';

	// grip.options = {
	// 	defaultRegexpAction: null, // function, only use after GRIT bootstrap
	// 	defaultPegAction: null     // function, only use after GRIT bootstrap
	// }

	grip._define = function() { // rule definitions
		// either a tag template or standard arguments....
		if (arguments.length === 0) return;
		if (this._compiled) throw new Error("*** grammar already defined..")
		if (!this._rules) this._init(); // define first rule(s)...
		var template = arguments[0]; // either a tag template or std args....
		if (template instanceof Array &&  template.raw) { // ES6 tag template...
			this._templateRules.apply(this, arguments); // avoids using ES6
		} else { // ES5 Grit(rule, rule, ...);
			var args = []; // to allow multi-line arg values...
			for (var i=0; i<arguments.length; i++) {
				var arg = arguments[i];
				args = args.concat(arg.split('\n'));
			}
			this._createRules(args); // may be none e.g. new Grit();
		}
		this._compile();
	}

	grip._init = function() { // new Grit, first call to define rules...
		this._rules = []; // define source text
		this._rule = {}; // compiled rules
		this._$Flag = false; // PEG $ rule trace
		this._action = {}; // action function, type translators
		this._actName = {}; // action function, function name...
		this._actArgs = {}; // action function, type translator arguments...
		this._actionTrace = {}; // action trace flag from grammar rule :: $
		this._actionTraceFlag = false; // any _actionTrace[rule] :: $ triggered
		this._matchAllInput = true; // true: throws error if not full match
	}

	grip._templateRules = function() { // vararg arguments...
		var template = arguments[0].raw; // ES6 tag template expected...
		var rules = "";
		var types = {};
		for (var i=0; i<template.length; i+=1) {
			if (i > 0 && arguments[i]) {
				var arg = arguments[i];
				if (typeof arg === 'string') {
					rules += arg;
				} else if (typeof arg === 'function') {
					rules += "<"+i+">";
					types[i] = arg;
				}
			}
			rules += template[i].replace(/\\`/g,'`').replace(/\\[$][{]/g,'${');
		}
		this._createRules(rules.split(/\n/), types);
	}

	grip._createRules = function(rules, types) {
		var errors = []
		for (var i = 0; i < rules.length; i++) {
			var rule = rules[i];
			if (!rule) continue;
			var rx = rule.match(RULE); // read full rule...
			if (rx) {
				var type = rx[2]; // := | :~
				var body = rx[3]; // ... :: ...
				while (i+1 < rules.length) { // ... more lines ...
					var nxtrule = rules[i+1].match(RULE); // avoid duplicate use of var rule
					if (nxtrule) break; // start of next rule...
					body += '\n'+rules[i+1];
					i += 1;
				}
				var act = null, pax = null;
				if (type===PEG_RULE) { // .... ' :: ' ... :: ....
					pax = body.match(/^((?:[^:']|:[^:]|'[^']*')*)::\s*([\s\S]*)/);
				} else if (type===REGEXP_RULE) { // ... :: ...
					pax = body.match(/^((?:[^:]|:[^:])*)::\s*([\s\S]*)/);
				}
				if (pax) { // ... :: act...
					body = pax[1];
					act = pax[2];
					var nx = act.match(/<(\d+)>/);
					if (nx) act = types[nx[1]];
				}
				this._rules.push( { name: rx[1], type: type, body: body, act: act } );
			} else {
				errors.push("Bad rule format: "+rule)
				// console.error(errors[errors.length-1])
			}
		}
		if (errors.length>0)
			throw new Error(errors.join('\n\t'))
	}


// compile rules ----------------------------------------------------------------------

	grip._compile = function() {
		if (this._compiled) return [];
		var errors = this._compileRules();
		if (errors.length > 0) {
			errors.unshift(this._rules[0].name + " grammar errors:");
			throw new Error(errors.join('\n\t'));
		}
		this._compiled = true;
		// return errors;
	}

	grip._compileRules = function () {
		var errors = [] // to collect errors
		var unlinked = []; // RegExpr rules with %name not yet resolved...
		for (var i=this._rules.length-1; i>-1; i--) {
			var rule = this._rules[i];
			if (rule.type === REGEXP_RULE) {
				try {
					var rex = this._makeRegExp(rule);
					if (rex) this._rule[rule.name] = new RegExp("^(?:"+rex+")", "g");
					else unlinked.push(i);
				} catch(err) {
					error(["Rule ", rule.name,
						" has invalid RegExp /", rule.body.trim(),  "/ : ", err])
				}
			} else if (rule.type === PEG_RULE) {
				if (rule.body.match(/\s+[$]($|\s+)/)) this._$Flag = true
				this._rule[rule.name] = GRIT.parse(rule.body);
			} else if (rule.type === FUN_RULE) { // name :: action
				this._rule[rule.name] = function(content, args) {
						// this.pos = this.pos + content.length;
						// return [content, args];
						return [];
					};
				rule.act = rule.body;
			} else {
				error(["Rule ", rule.name, 'has undefined type ', rule.type])
			}
			if (rule.act) {
				var act = rule.act;		// console.log(typeof act, ' action:', act)
				if (typeof act === 'string') {
					var flag = act.match(/^\s*\$\s*/); // $ trace flag
					if (flag) {
						act = act.slice(flag[0].length);
						if (!act) act = "(...args) => args";
						this._actionTrace[rule.name] = true;
						this._actionTraceFlag = true;
					}
					try {
						this._action[rule.name] = this._compileAction(rule, act);
					}  catch(err) {
						error(["Rule ", rule.name, " ... :: ", act,
							'\tBad action function ', err])
					}
				} else if (typeof act === 'function') {
					this._action[rule.name] = act;
				} else retport(["Rule ", rule.name, " ... :: ", act,
					'\tUnknown action function Object?'])
			} else { // default action...  null for GRIT bootstrap...
				if (rule.type === REGEXP_RULE)
					this._action[rule.name] = this._defaultRegAction;
				else if (rule.type === PEG_RULE)
					this._action[rule.name] = this._defaultPegAction;
			}
		}
		while (unlinked.length>0) { // unresolved %name references..
			var residual = []; // if still not resolved..
			for (var i=0; i<unlinked.length; i+=1) {
				var rule = this._rules[unlinked[i]];
				var rex = this._makeRegExp(rule);
				if (rex) this._rule[rule.name] = new RegExp("^(?:"+rex+")", "g");
				else residual.push(unlinked[i]);
			}
			if (residual.length === unlinked.length)
				throw new Error("Unresolved %rule reference in rule: "
					+unlinked.map((m,i)=>this._rules[unlinked[i]].name))
			unlinked = residual; // try again...
		}
		return errors

		function error(errMessage) {
			var errString = errMessage.join('')
			errors.push(errString)
		}
	}

// compile action function function -----------------------

	grip._compileAction = function (rule, act) {
		var fn;
		var ax = act.match(/^\s*(&?[a-zA-Z]\w*)\s*(.*)$/)
		if (!ax) { // (..) => ... or ( ... ) or // ..anything else..
			fn = eval(act);
		} else {
			var fun = ax[1]; // function name or &rule ref...
			if (fun === 'function') { // :: function(...) {... }
				fn = eval('(' + act + ')');
			} else { //  :: fun .... => grit.action may not yet be defined
				this._actName[rule.name] = fun; // grammar function name..
				this._actArgs[rule.name] = ax[2]; // arg string
				fn = fun;
			}
		}
		return fn; // function, or string (name of function)
	}

// compose RegExp rule -------------------------------------

	grip._makeRegExp = function (rule) {
		var that = this;
		var txt = rule.body.trim();
		var unlinked = false; //
		txt = txt.replace(/%[a-zA-Z]\w*/g, function(name) {
			var rex = that._rule[name.slice(1)]; // defined rule
			if (rex instanceof RegExp) { // leaf rule
				return rex.toString().slice(2,-2); // /^.../g
			} else {
				unlinked = true; // unresolved %name link...
				// console.log("Undefined rule: "+name+" in: "+txt);
			}
			return name; // ignore this one, for now (unlinked)
		});
		if (unlinked) return null;
		// delete white space, but prserve space in [chars]
		txt = txt.replace(/\\[\s\S]|\[([^\]\\]*(\\[\s\S])?)*\]|\s+/g, function(span) {
			var c = span[0]; // check for \s+
			if (c === ' ' || c === '\t' || c === '\n' || c === '\r') {
				return ''; // delete white-space
			} // don't delete space chars inside [...] or after esc \
			return span; // preserve as-is
		});
		return txt;
	}

// Parser  -------------------------------------------------------------

	// grip.parse = function (input) {
	// 	return this._parse(new Parser(this, input))
	// }
	// 
	// grip.parse_trace = function (input) {
	// 	var p = new Parser(this, input)
	// 	p._traceFlag = true;
	// 	return this._parse(p)
	// }
	// 
	// grip._parse = function (parser) {
	// 	// this._lastMatch = null;

	grip.parse = function (input) {
		var parser = new Parser(this, input);
		var begin = this._rules[0]; // start at first rule...
		if (!begin) throw new Error("Parsing with empty grammar, no rules defined.")
		if (!this._compiled) throw new Error("*** woops... grammar not compiled?..")

		var input = parser.input
		if (typeof input !== 'string') throw new Error("Grit parse input is not a string...");

		parser.result = parser.parseRule(begin.name);

		// if (parser.result != FAIL) this._lastMatch = input.substr(0, parser.pos)

		if (this._matchAllInput && (parser.pos < input.length) && !input.slice(parser.pos).match(/^\s*$/)) {
			parser.reportPos(parser.pos, parser._maxFail,"!"+parser._maxRule+
			" ... parse fell short ..."); // fault report...
			throw new Error(["Grammar ", begin.name," parse fell short ["+
				parser.pos+"-"+parser._maxFail+"]:\n\t", input].join())
		}

		return parser.result;
	}

	// Parser -------------------------------------------------------------

	var RULEMAX = 100; // max rule depth, to catch looping..

	var Parser = function(grit, input) {
		this.grit = grit; // grammar rules
		this.input = input;
		this.pos = 0;
		this._traceFlag = grit._$Flag || grit._actionTraceFlag;
		this._trail = []; // trace stack
		this._last = {}; // rule result memos
		this._maxFail = -1; // maxFail pos
		this._maxRule = undefined; // maxFail rule name
		this._rulecount = 0; // catch RULEMAX loops...
	}

	Parser.prototype = Object.create(Grit.prototype);

	Parser.prototype.trace = function (flag) {
		this._traceFlag = !!flag
		return this;
	}

	Parser.prototype.parseRule = function (name) {
		var start = this.pos;
		var result = FAIL;
		if ((this._rulecount+=1) > RULEMAX) this._traceFlag = true; // looping...
		if (this._traceFlag) {
			this._trail.push(name);
			if (this._rulecount > RULEMAX+5) {
				this.reportTrace();
				throw new Error("Rule depth overflow using grammar "+this.grit._rules[0].name);
			}
		}
		var rule = this.grit._rule[name];
		if (!rule) rule = this.resolveRule(name);
		if (rule instanceof RegExp) {
			result = this.leafNode(name, rule);
		} else if (typeof rule === 'function') {
			result = rule.call(this)
			// , this.input.slice(start), this.grit._actArgs[name], start, name );
		} else if (rule instanceof Array) { // Grit.parse() tree
			result = GRIT.exec(this, rule); // GRIT grammar **** Grit grit ****
		} else {
			throw new Error(["Rule ", name, "invalid:\n\t ", rule].join(''))
		}
		this._rulecount -= 1;
		if (result !== FAIL) {
			// var node = this.ruleNode(result, name, start); // array node;
			// this._last[name] = node; // TODO node to use as pack-rat memo
			var action = this.grit._action[name]; // function or unresolved actionName
			if (typeof action === 'string') action = this.resolveAction(name, action);
			var product = result; // or result from action...
			if (action) {
				try {
					product = action.apply(this, result);
				} catch (err) {
					throw new Error(["Rule ", name, " :: action function failed:\n\t", err].join(''));
				}
				if (this.grit._actionTraceFlag && this.grit._actionTrace[name]) {
					this.reportTrace(start, product);
				}
				// if (product === null || product === undefined) product = FAIL;
				if (product === undefined)
					throw new Error("undefined action result in: "+name+' ... :: '+action)
				if (product === null) product = FAIL;
			}
			if (this._traceFlag) {
				if (!this.grit._$Flag && !this.grit._actionTraceFlag)
					this.reportTrace(start, product);
				this.traceClean(1);
			}
			if (product !== FAIL) { return product; }
		}
		if (this._traceFlag) { this._trail.push("!"); }
		if (start > this._maxFail) {
			this._maxFail = start; // for: ^  ^ fault report span
			this._maxRule = name;
		}
		return FAIL;
	}

	Parser.prototype.resolveRule = function(name) {
		var rule = this.grit[name] || Grit.prototype[name];
		if (!rule)
			throw new Error(["Undefined rule: ", name, " in grammar ", this.grit._rules[0].name].join(''))
		this.grit._rule[name] = rule; // resolved rule name
		return rule; // rule function
	}

	Parser.prototype.resolveAction = function(name, actionName) {
		var action, refx = actionName.match(/^&(\S+)/);
		if (refx) { // &rule ref...
			if (this.grit._rule[refx[1]]) {
				action = this._and_Rule(name, refx[1])
			} else throw new Error("Rule "+name+" ... :: "+actionName+
					"\tUndefined rule reference..");
		}
		action = action || this.grit[actionName] || Grit.prototype[actionName];
		if (typeof action !== 'function') {
			throw new Error("Rule "+name+" ... :: "+actionName+
					"\tBad action function: function expected..")
		}
		this.grit._action[name] = action; // resolve actioo => function
		return action; // action function..
	}

	Parser.prototype._and_Rule = function(ruleName, ruleRef) { // :: &rule
		return function (str) { // action function, this = parser
			if (typeof str !== 'string')
				throw new Error("Rule "+ruleName+" ... :: &"+ruleRef+
					"\tBad argument, expecting a string..");
			var pos = this.pos, input = this.input
			this.pos = 0, this.input = str;
			var result = this.parseRule(ruleRef);
			if (this.pos!==str.length) result = FAIL;
			this.pos = pos, this.input = input;
			return result;
		};
	}

	Parser.prototype.traceClean = function (n) {
		if (n < 1 && this._trail[this._trail.length-1] !== '!') return;
		var x = this._trail.pop();
		n = (x === '!')? n+1 : n-1;
		this.traceClean(n);
	}

	// Parser.prototype.ruleNode = function (node, name, start) { // TODO fix jul19, 2015 for metamark
	// 	node.rule = name;
	// 	node.index = start;
	// 	// node.input = this.input;
	// 	node.lastIndex = this.pos;
	// 	return node;
	// }

	Parser.prototype.leafNode = function (name, regex) {
		regex.lastIndex = 0; // reset index
		var mx = regex.exec(this.input.slice(this.pos));
		if (!mx) return FAIL;
		mx.rule = name;
		if (mx.input.length > 6) mx.input = mx.input.slice(0,3)+'...'
		// mx.input = null; // clutter in trace, redundant info.. or delete?
		mx.index = this.pos; // more useful for debug..
		this.pos += mx[0].length;
		return mx;
	}

// -- parser trace reporting -------------------------------------------------

	Parser.prototype.report = function (report) {
		// this should be the ONLY place reports are printed
		var s = this.string(report) // flatten
		s = s.replace(/[\t]/g,'›').replace(/[\n\r]/g,'¬')
		s = s.replace(/[\x00-\x1F]/g,'◊')
		console.log(s) // Future plan: enable other report output
	}

	Parser.prototype.reportTrace = function (start, result) {
		if (!start) start = this.pos;
		var posn = (!start || start===this.pos)? start+" " : start+'..'+this.pos+" ";
		var trail = posn+this._trail.join(' ');
		this.reportPos(start, this.pos, trail);
		if (result) this.report(["=> ", result]);
	}

	Parser.prototype.reportPos = function(start, pos, trail) { // report pos...
		if (!start && start!==0) start = pos = this.pos
		if (!pos && pos!==0) pos = this.pos
		if (!trail) trail = this._trail.join(' ')
		var txt = this.input;
		var sp = "                                                           ";
		var span = "";
		var k = (pos-start > 40)? pos : start;
		if (pos>k) span = sp.slice(0,pos-start-1)+"^"; // ^ ...span... ^
		span += " "+trail;
		var report
		if (k>30) {
			this.report(["...", txt.slice(k-30,k+30)])
			this.report([sp.slice(0,33), "^", span])
		} else {
			this.report([txt.slice(0,k+64)])
			this.report([sp.slice(0,k), "^", span])
		}
		return true;
	}


//  == Grit grammar bootstrap =============================================

// GRIT instance to parse Grit grammar rules.....

	var GRIT = new Grit(
		// these four functions are a hand coded bootstrap
		// " exp   := seq ('/' seq)* ",
		// " seq   := (pred? term rep?)+ ",
		// " term  := rule / quote / group ",
		// " group := '(' exp ')' ",
		" exp   :~ \\s* ", // dummy start rule to begin
		" pred  :~ \\s* ([&!]) ",
		" rep   :~ ([+*?]) \\s* ",
		" rule  :~ \\s* ([a-zA-Z$_]\\w*) \\s* ",
		" quote :~ \\s* (?: ['] ([^']+) ['] | [\"] ([^\"]+) [\"]) \\s* "
	);

	GRIT._rule.exp = function () {
		var start = this.pos; // this = parser
		var seq = GRIT._rule.seq.call(this);
		if (seq === FAIL) return GRIT._faultReport(this);
		var exp = []; // result node..
		exp.rule = 'exp';
		while (seq !== FAIL) {
			exp.push(seq);
			if (!this.leafNode("",/^\s*\/\s*/g)) break;
			seq = GRIT._rule.seq.call(this);
		}
		if (start === 0 && (this.pos < this.input.trim().length)) {
			return GRIT._faultReport(this);
		}
		return exp;
	}

	GRIT._rule.seq = function () { // seq := (pred? term rep?)+
		var start = this.pos;
		var terms = [];
		while (true) {
			var pos = this.pos;
			var pred = this.parseRule('pred') || []; // pred?
			var term = GRIT._rule.term.call(this);
			if (term === FAIL || this.pos === pos) break;
			terms.push(pred);
			terms.push(term);
			var rep = this.parseRule('rep') || []; // rep?
			terms.push(rep);
		}
		if (terms.length < 1) {
			this.pos = start;
			return FAIL;
		}
		terms.rule = 'seq';
		return terms;
	}

	GRIT._rule.group = function () {
		if (!this.leafNode("",/^\s*[(]\s*/g)) return FAIL;
		var res = this.parseRule('exp');
		if (!this.leafNode("",/^\s*[)]\s*/g)) return FAIL;
		return res;
	}

	GRIT._rule.term = function () {
		var result = this.parseRule('rule');
		if (result !== FAIL) return result;
		result = this.parseRule('quote');
		if (result !== FAIL) return result;
		return this.parseRule('group');
	}

	GRIT._faultReport = function (parser) { //rule, input, pos
		var rule = parser.grit._rules[0];
		var input = parser.input;
		var pos = parser.pos;
		var nametype = rule.name+" "+rule.type+" ";
		this.report("Bad rule: "+nametype+input);
		var sp = "                                                           ";
		this.report("          "+sp.slice(0,nametype.length+pos)+"^");
		return FAIL;
	}


// -- exec => parse with rule parse tree ---------------------------------------

	GRIT.exec = function (parser, ruleTree) {
		var fn = this.do[ruleTree.rule]; // GRIT rule do functions
		if (fn) return fn.call(this, parser, ruleTree);
		throw new Error("Grit exec missing do function for: "+ruleTree.rule)
		// this.report("Grit exec missing do function for: "+ruleTree.rule);
		// return FAIL;
	}

	GRIT.do = {};

	GRIT.do.exp = function (parser, ruleTree) { // exp -> seq ('/' seq)*
		var start = parser.pos;
		for (var i=0; i<ruleTree.length; i++) {
			var seq = this.exec(parser,ruleTree[i]);
			if (seq !== FAIL) return seq;
			parser.pos = start;
		}
		return FAIL;
	}

	GRIT.do.seq = function (parser, ruleTree) { // seq := (pred? term rep?)+
		var start = parser.pos;
		var terms = [];
		for (var i=0; i<ruleTree.length; i+=3) {
			var nxt = parser.pos;
			var pred = ruleTree[i];
			var term = ruleTree[i+1];
			var rep = ruleTree[i+2];
			var result = this.exec(parser,term);
			if (pred.length>0) {
				if (rep.length>0)
				  throw new Error("Unexpected repeat operator: ",pred[0]+term+rep[0])
				  // console.log("Unexpected repeat operator: ",pred[0]+term+rep[0]);
				parser.pos = nxt; // zero advance...
				if ((pred[1] === '&' && result !== FAIL) ||
					(pred[1] === '!' && result === FAIL)) {
					terms.push([]);
					continue;
				}
				return FAIL;
			}
			if (rep.length>0) { // ?*+  rep?
				if (rep[1] === '+' && result === FAIL) {
					parser.pos = start;
					return FAIL;
				}
				var reps = [];
				while (result !== FAIL && parser.pos > nxt) {
					nxt = parser.pos;
					reps.push(result);
					if (rep[1] === '?') break;
					result = this.exec(parser, ruleTree[i+1]);
				}
				terms.push(reps);
				continue;
			}
			if (result === FAIL) {
				parser.pos = start;
				return FAIL;
			}
			terms.push(result);
		}
		return terms;
	}

	GRIT.do.rule = function (parser, ruleTree) { // \s* (rule) \s*
		return parser.parseRule(ruleTree[1]);
	}

	GRIT.do.group = function (parser, ruleTree) {
		return this.do.exp.call(this, parser, ruleTree);
	}

	GRIT.do.quote = function (parser, ruleTree) {
		var qt = ruleTree[0].trim(); // 'xxx' or \s* "xxx"
		if (!parser.grit._rule[qt]) { // define a new rule for qt...
			var str = ruleTree[1] || ruleTree[2]; // '...' | "..."
			var literal = str.replace(/([^a-zA-Z0-9])/g,"\\$1")
			var sp = ruleTree[2]?'\\s*':''
			var regex = new RegExp("^(?:"+sp+"("+literal+")"+sp+")");
			parser.grit._rule[qt] = regex;
			parser.grit._action[qt] = (_, x) => x;
		}
		return parser.parseRule(qt);
	}

// Helper functions ............................................

	//  ---  string, number ..........................

	grip.string = function (...ts) {
		return this.flatten(ts).join('')
	}

	grip.number = function (...ts) {
		return Number(this.flatten(ts).join(''))
	}

	//  ---  flatten ..........................

	grip.flatten = function flatn(arr) {
		if (!Array.isArray(arr)) return arr;
		return arr.reduce((a, b) => a.concat(flatn(b)), []);
	}

	// grip.flatten = function flatn(arr) {
	// 	return arr.reduce((a, b) =>
	// 	  a.concat(Array.isArray(b) ? flatn(b) : b), []);
	// }

	// flatten array prototype.... ??

	if (!Array.prototype.flatten) {
		Array.prototype.flatten = function () {
	    	return this.reduce(function (a, b) {
	        	return a.concat(Array.isArray(b) ? b.flatten() : b);
	    	}, []);
		}
	};

	// user trace ...........................

	grip.$ = function () {
		this.reportTrace();
		return []; // not FAIL
	}

	// :: simplify => flatten to simple list(s)...

	grip._simplify = function simplify (...ts) {
		if (ts.length===1) { // [[[x]]] => x
			var x = ts[0];
			if (!Array.isArray(x)) return x;
			return simplify(...x);
		}
		var i=ts.length-1; // [x,..z,[],..,[]] => [x,..,z]
		while (i>0 && Array.isArray(ts[i]) && ts[i].length===0) i -= 1;
		var rs = [];
		for (var k=0; k<=i; k+=1) rs.push(simplify(ts[k]));
		if (rs.length===1) return rs[0];
		return rs;
	};

	// Action defaults -- must be after GRIT bootstrap .........

	grip._defaultRegAction = (x) => x;
	grip._defaultPegAction = null; //grip._simplify;


	// user extensions...........................

	Grit.use = function (actions) {
		var funs; // action functions
		if (typeof actions === 'string') { // reuire file name or module...
			if (typeof require === 'function') {
				funs = require(actions) // exports.fn ...
			} else throw new Error("Grit.use( {name:fn, ...} ), 'require' is not available...")
		} else funs = actions; // {fn...} 
		for (fn in funs) grip[fn] = funs[fn]
	}


// == Expose Grit ==============================================================

	if (typeof module !== 'undefined' && typeof exports === 'object') {
		module.exports = Grit;
	} else if (typeof define === 'function' && define.amd) {
		define(function() { return Grit; });
	} else {
		this.Grit = Grit;
	}

}).call(function() {
	return this || (typeof window !== 'undefined' ? window : global);
}());

// console.log("grit.js.....");
