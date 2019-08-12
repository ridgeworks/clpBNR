// -- markit: framework module for publishing MyWord markup ----

/*	The MIT License (MIT)
 *
 *	Copyright (c) 2016,2017,2018 Peter Cashin, Rick Workman
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

;(function () {
	
	// if necessary, a shim for Array.flat() 
	if (typeof Array.prototype.flat == 'undefined')
		Array.prototype.flat = function(depth) {
			if ((typeof depth == 'undefined') || depth==1)
				return [].concat.apply([], this)  // efficient shallow flatten
			else if (depth == Infinity)
				return flattenDeep(this)          // deep flatten
			else if (depth > 1)                   // intermediate flatten
				return this.reduce(
					(acc, item) =>
						acc.concat(Array.isArray(item) ? item.flat(depth-1) : item),
					[]
					)
			else return this                     // no flatten

			function flattenDeep(arr) {  // could be made into an Array method
				return arr.reduce(
					(acc, item) =>
						acc.concat(Array.isArray(item) ? flattenDeep(item) : item),
					[]
				)
			} // flattenDeep(arr)
		} // Array.prototype.flat(depth)


	/*
	 *  0. I/O support: {
	 *        setLoadPath(filepath)                     :: String -> undefined
	 *        processURL(url, process, idempotent)      :: String -> Function -> Boolean -> String
	 *     }
	 */

	const io = function () {
		var loadpath = [''];               // base for relative URLs, acts like a stack
		var loaded = {}                    // save idempotent loaded items as absurl
		
		function directory(url) {
			return url.substring(0, url.lastIndexOf('/') + 1)
		} // directory(url)

		function composeURL(url) {      // only called from processURL
			return /^\/|:\/\//.test(url)  // starts with '/' or contains '://'
				? url                 // partial or absolute URL
				: loadpath[0] + url   // relative URL
		} // composeURL(path)

		function fileContent(url) { // returns content or throws exception, only called from processURL
			var status = 0;
			if (typeof XMLHttpRequest != 'undefined') {
				var request = new XMLHttpRequest();
				//request.withCredentials = true
				request.open("GET", url, false);   //synchronous IO, requires Worker mode in browsers
				request.setRequestHeader("Accept","text/*,*/*")
				request.onerror = function () {
					status = 404
				};
				request.send();
				status = ((status == 0) ? request.status : status );
				if ((status === 200 || status === 0)) {
					return request.responseText
				} else {
					throw new Error(["HTTP status=", status].join(''));
					//ES6: throw new Error(`Reading '${url}' status=${status}`)
				}
			} else {	// try Nodejs file system
				return fs.readFileSync(url, "utf8");
			}
		} // fileContent(url)
		
		function processURL(url, process, idempotent) {
			var out = ''
			const absurl = composeURL(url.trim());
			if (!idempotent || (typeof loaded[absurl] === 'undefined')) {  // if idempotent and loaded, return ''
				loadpath.unshift(directory(absurl))      // push new loadpath
				try {
					out = process(fileContent(absurl), absurl)
					if (idempotent) loaded[absurl] = true
				} catch (err) {
					// a bit of a circular dependancy here, but isolated and pretty safe
					out = core.newNode('errorString', ["Reading '", absurl, "':\n\t", (err.message || err.name) ].join(''))
				}
				loadpath.shift()                        // pop loadpath
			}
			return out
		} // processURL(url, process)
		
		function setLoadPath(filepath) {
			loadpath = [directory(filepath)]
		} // setLoadPath(filepath)

		return {
			processURL: processURL,
			setLoadPath: setLoadPath
		}
		
	}()	// const io
	
	Object.freeze(io)			// freeze io


	/*
	 *  1. Init environment - load Grit and if executing as a Worker, setup message handler
	 *  	Note, due to syncIO, file ops only work in Worker mode
	 */

	const workerMode = function() {
		try {
			return (self instanceof WorkerGlobalScope)  // true if functioning as a Worker
		} catch (err) {
			return false
		}
	} ()
	
	const workerID = (workerMode) ? Date.now() : '';   // a given Worker instance or ''
	
	const Grit = function(worker) {                    // a reference to Grit
		if (worker) {
				// Note extension code must insert _extensionHref in WorkerGlobalSpace if different from location.href
				io.setLoadPath((typeof _extensionHref === 'undefined') ? location.href : _extensionHref)
				if (typeof self.Grit === 'undefined') try {  // if Grit not bundled
					io.processURL("grit.js", function(content){
					const geval = eval;
					geval(content);	// eval() in global scope, independent of module scheme
					return ''
				})
			} catch (err) {
				throw new Error(["loading grit.js: ", err.message].join(''))
			}
			return self.Grit;
		} else { // assumes Node.js, or something else that supports 'require'
			try {
				require('fs');	// TODO is there a better place for this?load fs for io
				return require("./grit.js");  // Load Grit - grit.js assumed to be co-located
			} catch (err) {
				throw new Error(
					["Unsupported platform - upgrade browser or use CommonJS module system: ", err.message].join('')
				)
			}
		}
	} (workerMode);
	
	if (workerMode) {                          // When used in Worker mode:
		global = self; window = global           // "globals" for Worker unaware imports
		onmessage = function (msg) {             // global onmessage handler
			// msg.data[0]:#id, msg.data[1]:type, msg.data[2]:content, msg.data[3]:contextID, msg.data[4]:base url,
			io.setLoadPath(msg.data[ 4 ])
			core.useContext(msg.data[ 3 ])
			postMessage([ msg.data[ 0 ],
				(msg.data[ 1 ] === 'metamark')
					? markit.setDefaultLingo(msg.data[ 2 ])
					: markit(msg.data[ 1 ], msg.data[ 2 ])   // see markit() for spec
			])
		} // onmessage(msg)
	}
	
	if (console) console.log("Worker:" + workerID);

	/*
	 *  2. core object containing framework API : {
	 *        markit:           function(type, content, parms)         :: String -> String -> String -> String
	 *        applyLabel:       function(label, content, defaultType)  :: String -> String -> String -> String
	 *        newNode:          function(type, content, label)         :: String -> String -> String -> Node
	 *        renderNodes:      function(nodes)                        :: Array(Node..) -> String
	 *        metamarkAdd:      function(metamark)                     :: String -> String
	 *        contextID:        function()                             :: _ -> String
	 *        useContext:       function(contextID)                    :: String -> undefined
	 *        addBaseType:      function(type, transform)              :: String -> Function -> undefined
	 *        setDefaultLingo:  function(lingo)                        :: String -> String
	 *     }
	 *        Node:             See newNode() declaration
	 */

	const core = function() {

		/*
		 *  Context class for managing defs
		 */

		const Ctx = function (parent) {
			this.parent = parent;  // link to parent context, null if root
			this.index = {};       // label to dataType map
			this.types = {};       // dataType to transform map
			this.closed = 0;       // 0: can be written, >0: can't be written
			                       //    support for lazy context push - can't add if closed >0
		}; // new Ctx(parent)

		Ctx.prototype = {};
		
		// add new label definition : (success returns the label definition; duplicates return null and are ignored)
		Ctx.prototype.addLabelDef = function (label, labelDef) {
			const labelKey = label.replace(/\s+/g, ' ') // for key matching, white space is equivalent to a single space
			if (this.index[labelKey]) return null       // duplicate definition
			this.index[labelKey] = labelDef
			return labelDef
		}; // Ctx.addLabelDef(label, dataType)

		// lookup label definition associated with a label
		Ctx.prototype.labelDef = function (label) {
			const ldef = this.index[label.replace(/\s+/g, ' ')];  // for key matching, white space is equivalent to a single space
			return (typeof ldef === 'undefined')
				? ((this.parent) ? this.parent.labelDef(label) : null)
				: ((ldef==='') ? null : ldef)  // empty string signifies an (temporarily) undefined label
		}; // Ctx.labelDef(label)

		// add new type definition (success returns the type definition; duplicates return null and are ignored)
		Ctx.prototype.addTransform = function (type, transform) {
			if (this.types[type]) return null  // duplicate definition
			this.types[type] = transform
			return transform
		}; // Ctx.addTransform(type, transform)

		// lookup a transform associated with type
		Ctx.prototype.transform = function (type) {
			return type ? (this.types[type] || (this.parent ? this.parent.transform(type) : null)) : null
		}; // Ctx.transform(type)

		// for context management in markit()
		Ctx.prototype.closeContext = function () {
			this.closed ++          // close for new defintions
			return this             // return current context
		} // Ctx.closeContext()
				
		// for context management in markit()
		Ctx.prototype.reopenContext = function () {
			// if open pop it for new current, then decrement close count return it
			var reopened = (this.closed === 0) ? this.pop() : this
			reopened.closed --
			return reopened
		} // Ctx.reopenContext()

		// primitive op - create a new (nested) context
		Ctx.prototype.push = function () {
			return new Ctx(this)
		}; // Ctx.push(blks)

		// primitive op - return parent context
		Ctx.prototype.pop = function () {
			return this.parent
		}; // Ctx.pop()

				
		Object.freeze(Ctx)
		
		var context = new Ctx(null);  // Create empty root context
		
		/*
		 *  Wrapper functions for adding definitions. Lazy push a new context if current context closed.
		 *  Hides context from metamark. Note adding CSS must also push a new context.
		 */
		function addTransform(type, transform) {
			if (context.closed > 0) context = context.push()
			return context.addTransform(type, transform)
		} // addTransform(type, transform)

		function addLabelDef(label, labelDef) {
			if (context.closed > 0) context = context.push()
			return context.addLabelDef(label, labelDef)
		} // addLabelDef(label, labelDef)
		
		function addCSS(css) {
			if (context.closed > 0) context = context.push()
			return css
		} // addCSS(css)
		
		

		// Basic error formatting type required for internal use but exported for general use.
		addTransform('errorString', function (content) {  // type defintion for error messages
			if (console) console.error(["markit(", workerID, "):", content].join(''));
			return ["\n*** Error *** ", content, "\n"].join('')
		});
		
		/*
		 *  Global API function : markit(type, content, parms)
		 *  returns the string result of calling the transform - may be an errorString
		 */

		const markit = function(type, content, parms) {
			var output
			if (type) {
				const transform = context.transform(type);
				if (transform) {
					context.closeContext()  // close the current context
					try {
						output = transform.call(null, content, parms);
						output = (typeof output === 'string')  // Expecting a string result
							? output
							: markit('errorString', [" bad result from transform for type ", type, " => ", JSON.stringify(output)].join(''))
					} catch (err) {
						output = markit('errorString', [" in transform for type '", type, "':\n\t", err.message ].join(''))
					}
					context = context.reopenContext()  // restore context, if necessary
				} else output = markit('errorString', [" transform for type '", type, "' not defined."].join(''))
			} else output = markit('errorString', [" illegal type '", JSON.stringify(type), "'"].join(''))
			return output
		} // markit(type, content, parms)

		/*
		 *  Nodes represent a deferred call to markit and are created by parser semantic actions
		 *    Node: {type:aTypeName, content:aString, label:aLabel}
		 */
		function newNode(typeName, content, label) {
			return {type:typeName, content:content, label:label}
		}

		/*
		 *  Utility function to render a node list to a string using markit()
		 *    render(aNode) ==> markit(anode.type, anode.content, anode.label)
		 */
		function renderNodes(nodeList) {       // :: [Node..] -> String
			return renderNode(nodeList).join('')
			
			function renderNode(node) {
				return Array.isArray(node)
					? node.reduce((acc, cnode) => acc.concat(renderNode(cnode)), [])
					: ((node.type) ? markit(node.type, node.content, node.label) : [])
			}
		} // function renderNodes(nodeList)
		

		/*
		 *  'metamark' parser for label and type defintions
		 */

		/* Comments and alternatives:
			// Note: metaword internal rule order is important because labeldef could match func/gram containing %ws<-%ws

			//labeldef   :~ (%word(?: (?! %EQ) %ws %word)*) %EQ (?:%defsep(%tag))? (?:%defsep(%block))? %nl?
			//                                         :: label(def,label,tag,transform)
			//EQ         :~ %ws <- (?= %defsep (?: <[a-zA-Z] | &[#a-zA-Z0-9] | [a-zA-Z]))
		*/
		const metaword = Grit`
			metaword   := (blank / fundef / gramdef / labeldef / uses / js / css / doc / comment / undefined)*
			blank      :~ [ \t]* %nl                :: (_) => []
			fundef     :~ (%name)\s+:{2}(%block)    :: func(_,type,func)
			gramdef    :~ (%name)\s+:%block         :: gram(rules,rule)
			labeldef   :~ (%word %line) %ws<- (?:%defsep(%tag))? (?:%defsep(%block))? (?: %nl | $)
			                                        :: label(def,label,tag,transform)
			defsep     :~ (?:%ws?%nl)?%ws
			uses       :~ @import(\s+%block)        :: uses(_,urls)
			js         :~ @javascript \s+ (%block)  :: js(_,js)
			css        :~ @css \s+ (%block)         :: css(_,css)
			doc        :~ @doc \s+ (%block)         :: doc(_,doc)
			comment    :~ // %line (?: %nl | $)     :: (_) => []
			undefined  :~ [ \t]* [^\n\r]+           :: undefined(statement)
			tag        :~ (?: [<](?:[^>\n\r]|(?:%nl\s))*[>]) | (?:&[#a-zA-Z0-9]*;)
			block      :~ %line %insetline*
			insetline  :~ (?: [ \t]* %nl | (%ws %line))
			word       :~ \S+
			name       :~ [a-zA-Z]\w*
			line       :~ [^\n\r]*
			ws         :~ [ \t]+
			nl         :~ (?:\r \n? | \n)
		`;

		metaword.label = function (definition, label, tagInfo, typeInfo) {
			// label(def,label,tag,transform)
			// construct label definition: { tag:tagString, etag:endTag, type:typeName, parmString:parms}
			const tag = ((tagInfo) ? tagInfo.trim().replace(/\s+/g, " ") : "");  // replace instances of whitespace with single space
			const etag = (tag && (tag[0]==='<') && (tag.substr(-2) !== '/>'))
				? ["</", tag.match(/^<\s*(\S+)[^>]*>$/)[1], ">"].join('')
				: ''
			const transform = (typeInfo) ? typeInfo.trim() : ''
			// empty label defintions are empty strings signifying undefined
			// used to undefine a label that was defined in a parent context.
			// Duplicate labels (null returned from addLabelDef) flagged as errors
			const tSpec = /^(\S+)([\s\S]*)/.exec(transform) || ['', null, '']  // [0]=src,[1]=type,[2]=parmstring
			return (addLabelDef(label.trim(),
				(tag || transform)
					? {	tag: tag, etag: etag,
							type: tSpec[1],
							transform: function(c, defaultType) {
								return markit(tSpec[1] ? tSpec[1] : defaultType, c, tSpec[2].trim())
							}
						}
					: ''
			) !== null)
				? []
				: newNode('errorString', ["Duplicate definition for '", label, "' ignored.\n\t", definition.trim()].join(''))
		} // metaword.label(definition, label, tagInfo, typeInfo)

		metaword.func = function (_, type, func) {
			try {
				const geval = eval	// global eval
				const transform = geval(func)
				return (typeof transform === 'function')
					? ((addTransform(type, transform))
						? []
						: newNode('errorString', ["Duplicate definition for '",type,"' ignored.\n\t", func.trim()].join(''))
						)
					: newNode('errorString', ["Invalid transform for '", type, "', ", func.trim(), " is not a function."].join(''))
			} catch (err) {  // compile errors on new types
				return newNode('errorString', err.message)
			}
		}; // metaword.func(_, type, func)

		metaword.gram = function (rules, rule) {
			try {
				const gram = new Grit(rules);
				return addTransform(rule, function(content, parmString) {
					// if (parmString)
					// 	console.log("Warning: rule " + rule + " - transform parameters `" + parmString + "` will be ignored." )
					return gram.parse(content, parmString)
				})
					? []
					: newNode('errorString', ["Duplicate definition for '", rule,"' ignored.\n\t", rules.split('\n')[0]].join(''))
			} catch (err) {		// compile errors on new types
				return newNode('errorString', err.message)
			}
		}; // metaword.gram(rules, rule)
		
		metaword.uses = function (_, urls) {
			return urls.trim().split(/\s+/).map(function(url) {
				const fileSuffix = url.substring(url.lastIndexOf('.'))
				const importHandler = importHandlers[fileSuffix]
				return (importHandler)
					? io.processURL(url, importHandler.handler, importHandler.idempotent)
					: newNode('errorString', ["Importing '", url, "', unsupported file type: ", fileSuffix].join(''))
			})
		}; // metaword.uses(_, urls)

		metaword.js = function (_, js) {
			return newNode('metajs', js)
		}; // metaword.js = function (_, js)

		metaword.css = function (_, css) {
			return newNode('metacss', addCSS(css))
		}; // metaword.css = function (_, css)

		metaword.doc = function (_, doc) {
			return newNode('metadoc', doc)
		}; // metaword.doc = function (_, doc)

		metaword.undefined = function (statement) {
			return newNode('errorString', ["Unrecognized metaword statement:\n\t", statement].join(''))
			//ES6:                        `Unrecognized metaword statement: ${statement}`)
		}; // metaword.undefined(_, statement)

		function metamarkAdd(content) {
			try {       // all exceptions turned into errorString's
				return metaword.parse(content)
			} catch (err) {
				return newNode('errorString', err.message)
			}
		} // function metamarkAdd(content)

		const importHandlers = {
			'.mmk': {handler:metamarkAdd, idempotent: false},
			'.txt': {handler:metamarkAdd, idempotent: false},
			'.js' : {handler: function(content) {
					const geval = eval;
					geval(content);  // eval() in global scope, independent of module scheme
					return ''
				}, idempotent: true},
			'.css': {handler: (content) => newNode('metacss', addCSS(content)), idempotent: false}
		}

		// Default types for JS, CSS and doc - return error (override in default lingo for desired semantics)
		addTransform('metajs', function (content) {
			return markit('errorString', ['No handler for @javascript: ', content.substring(0,79), ' ...'].join(''))
		});

		addTransform('metacss', function (content) {
			return markit('errorString', ['No handler for @css: ', content.substring(0,79), ' ...'].join(''))
		});
		
		addTransform('metadoc', function (content) { return '' });  // @doc: no-op by default
		
		var contextList = [context]  // Initialize list of persistent, immutable contexts for dynamic updates

		/*
		 *  Utility function to prohibit calls if called from markit().
		 *	Note: This check is a little fragile as it depends on the format of the stack trace.
		 *       If it encounters an unknown format, it will permit the operation.
		 *       Function.caller cannot be used to build a call stack if recursion occurs
		 */
		function checksafe(name, operation) {  // :: String -> Function -> Any
			try {Error.stackTraceLimit = Infinity} catch (err) {}  // Required for Chrome (at least)
			const stackTrace = '\n' + new Error().stack
			return ((stackTrace.indexOf('\nmarkit@') === -1) && (stackTrace.indexOf('at markit ') === -1))
				? operation()
				: markit('errorString', name + ' cannot be used by a transform.')
		} // function checksafe(name, operation)

		
		return { // core API for internal use in module 'markit'
			// Global API function
			markit: function(type, content, parms) {
				return (arguments.length===1) // 'curry' the function if only one argument
					? function(content, parms) { return markit(type, content, parms) }
					: markit(type, content, parms)
			}, // markit(type, content, parms)
			// Global API for users of label defintions
			applyLabel: function () {  // wrapper function to contain recursionStack
				var recursionStack = []  // used to detect infinite loops in lingos
				return function (label, content, defaultType) {
					// return null if label undefined, else returns '' if content null, else apply labelDef
					const labelDef = context.labelDef(label.trim())
					if (labelDef === null)
						return null
					else if (content === null)
						return ''
					else { // label is defined and there is non-null content
						var output
						const marker = [label, content].join('\t')  // marker contains type and content
						if (recursionStack.indexOf(marker) >= 0) {  // if marker already on stack, there's a loop
							output = markit('errorString', [" Lingo bug, infinite loop applying label '", label, "' to: ", content].join(''))
						} else {
							recursionStack.push(marker)  // add call to recursionStack
							output = [labelDef.tag, labelDef.transform(content, defaultType ? defaultType : 'myword'), labelDef.etag].join('')
							recursionStack.pop()
						}
						return output
					}
				}
			} (), // => applyLabel(label, content, defaultType)
			newNode: newNode,
			renderNodes: renderNodes,      // render nodes from parse operation to a string (see renderNodes above)
			metamarkAdd: metamarkAdd,      // add meta-content
			contextID: function () {
				if (context.closed === 0) {  // calculate a conditional contextID if context open (new definitions)
					contextList.push(context)  // persistant context for dynamic updates
					return (contextList.length-1).toString()
				} else
					return ''
			}, // contextID()
			 // Internal module API to support dynamic content, initialization of base types and (re)setting the default lingo.
			useContext: function (contextID) {  // *** This cannot be called from via markit(), directly or indirectly
				checksafe("useContext()", function (){
					context = contextList[parseInt(contextID)]  // see if contextID can be used as index to persistant list
					if (context == undefined) context = contextList[0]
				})
			}, // useContext(contextID)
			addBaseType: addTransform,          // *** This can only be called during module initialization.
			setDefaultLingo: function(lingo) {  // *** This cannot be called from via markit(), directly or indirectly
				return checksafe('setDefaultLingo()', function () {
					while (context.parent !== null) context.pop()  // discard all but base context
					context.closeContext()      // make sure base context is closed
					context = context.push()    // push a new context for the default lingo
					contextList = [context]     // reset contextList with the default lingo
					return renderNodes(metamarkAdd(lingo))  // add the default lingo and process any returned nodes
				})
			}, // setDefaultLingo(lingo)
		}
	} ()	// const core
	
	// copy to module level for internal convenience
	const markit = core.markit
	const applyLabel = core.applyLabel
	const newNode = core.newNode
	const renderNodes = core.renderNodes
	
	/*
	 * Common utility for making various label patterns
	 */
	
	const BLOCK=0, SPAN=1, SYM=2, ESC=3  // four patterns

	function makePat(pat, start, end) {  // :: Integer -> String -> String -> String
		switch (pat) {
			case BLOCK: return [start, ' ..'].join('')
			case SPAN:  return [start, ' .. ', end].join('')
			case SYM:   return start
			//case ESC:   return [start, ' .'].join('')
			default:    return ''
		} // switch
	} // makePat(pat, start, end)

	/*
	 *  3. Transform for type: myword
	 *  create and translate prime syntax block elements
	 *  Block labels are assumed to be type names (i.e., rule names) with prefix '.'; unlabelled content is 'markup'.
	 */
	
	core.addBaseType('myword', function() {

		const myword = Grit`
			myword      := (metablock / markup)*
			metablock   := metalabel sep line indentblock?     :: metablock(type, _, line, block)
			markup      := content pmore* nl*                  :: (sline, lines, nls) => markit.newNode(
			                                                         'markup',
			                                                         [sline].concat(lines).concat(nls).join(''))
			metalabel   :~ &(?!\S)                             :: (_) => 'mmk'
			sep         :~ [ \t]*
			indentblock := (blkblank* insetline)*              :: (lines) => lines.reduce(
			                                                         (acc, indented) => [acc, indented[0].join(''), indented[1]].join(''),
			                                                         '')
			insetline   :~ %inset (%line)                      :: (_,line) => line
			line        :~ %content (?: %nl | $)
			blkblank    :~ (?!%inset) [ \t]* %nl
			pmore       := nl* !metalabel content              :: (nls, _, content) => nls.concat(content).join('')
			inset       :~ \t | [ ]{4}
			content     :~ (?:[^\n\r])*
			nl          :~ (?: \n | \r\n?)
		`;

		myword.metablock = function(type, _, line, block)  {  // metablock  := metalabel sep line indentblock?
			const content = (line.match(/^\\s+$/)?'':line) + (block ? block : '')
			return [newNode('metamark', content), core.metamarkAdd(content)]
		}

		return (content) =>  markit('scope', renderNodes(myword.parse(content)), core.contextID())  // 'myword' transform

	}())  // addBaseType('myword', ...)

	core.addBaseType('metamark', (content) => '')                    // meta-content not output
	
	core.addBaseType('scope', (content, contextID) => content)       // default for scope, just throw away contextID

	core.addBaseType('external', (url) =>                            // include content in external resource(s) using url suffix as type
		url ? io.processURL(url.trim(), (content, absurl) => markit(new URL(absurl).pathname.match(/.*[.](\S*)/)[1], content)) : ''
	)


	/*
	 *  4. Transform for private type (can be used but not overridden): «markup»
	 *  create and translate markup block elements; unlabelled content is 'paragraph' which contains 'prose'.
	 *  Note: the grammar contains a capture group back reference in the 'fencend' rule which would be
	 *  flagged as an illegal octal escape if ever run in 'script' mode. If that ever happens, use '\\1'.
	 */

	core.addBaseType('«markup»', function() {

		const markup = Grit`
			markup       := (insetblock / labeledblock / fencedblock / blankline / paragraph)*
			                                                    :: (nodes) => markit.renderNodes(nodes)
			insetblock   := insetline indentblock?              :: (line, block) => markit.newNode(
			                                                           'insetblock', 
			                                                           [line].concat(block).join(''),
			                                                           '')
			labeledblock := label sep line indentblock?         :: (label, _, line, block) => markit.newNode(
			                                                           'labeledblock',
			                                                           (line.match(/^\s+$/)?'':line) + (block ? block : ''),
			                                                           label)
			fencedblock  :~ (%fence) %sep (%line) ((?:(?!%fencend) %line)*) (?: $ | %fencend)
			                                                    :: (_, __, infostring, content) => markit.newNode(
			                                                           'fencedblock',
			                                                            content,
			                                                            infostring.trim())
			blankline    :~ %blank                              :: (s) => markit.newNode('blankline', s)
			paragraph    := (!(blank / inset / label / fence) line)+    
			                                                    :: (lines) => markit.newNode(
			                                                            'paragraph',
			                                                            lines.map((line) => line[1]).join(''))
			indentblock  := (blkblank* insetline)*              :: (lines) => lines.reduce(
			                                                         (acc, indented) => [acc, indented[0].join(''), indented[1]].join(''),
			                                                         '')
			insetline    :~ %inset (%line)                      :: (_,line) => line
			line         :~ [^\n\r]* (?: %nl | $)
			label        :~ \S+                                 :: (s) => ((pat = s+' ..') =>
			                                                        (markit.applyLabel(pat ,null) !== null) ? pat : null) ()
			blkblank     :~ (?!%inset) %blank
			fence        :~ [~\x60]{3,}
			fencend      :~ \1 %sep (?: %nl | $)
			inset        :~ \t | [ ]{4}
			blank        :~ [ \t]* %nl
			sep          :~ [ \t]*
			nl           :~ (?: \n | \r\n?)
		`;

		return (content) =>  markup.parse(content)      // '«markup»' transform

	}())  // addBaseType('«markup»', ...

	core.addBaseType('markup', (content) =>  markit('«markup»', content))   // global 'markup' default is '«markup»'

	core.addBaseType('labeledblock', (content, label) =>                    // labelledblock, apply label with default=myword
		applyLabel(label, content, 'myword'))

	core.addBaseType('insetblock', (content) => markit('myword', content))  // default insetblock is myword

	core.addBaseType('fencedblock', (content, infostring) => {              // fencedblock, (label) ? labelledblock : insetblock
		const pat = infostring.match(/(\S+)/) + ' ..'
		return markit.applyLabel(pat, null)
			? markit('labeledblock', content, pat)
			: markit('insetblock', content)
	})

	core.addBaseType('paragraph', (content) => markit('prose', content))     // default paragraph, just prose

	core.addBaseType('blankline', (content) => content)                      // default for line with just (optional) whitespace


	/*
	 *  6. Transform: proseParse(content)
	 *  create and translate inline elements
	 */

	core.addBaseType('«prose»', function() {

		const simpleProse = Grit`
			prose    := (span / symbol / text / ctl)*            :: (nodes) => markit.renderNodes(nodes)
			span     := sstart (nested/(!end content))+ end      :: span(bmark, xs, emark)
			nested   := nstart (nested/notq)+ end
			notq     := (!nstart !end content)*
			sstart   :~ %tag                                     :: s_begin
			nstart   :~ %tag                                     :: n_begin
			end      :~ %tag                                     :: end_
			symbol   :~ %symchar [\S]*                           :: symbol(symbol)
			text     :~ %symchar | [a-zA-Z0-9 ]+                 :: (c) => markit.newNode('text', c)
			content  :~ [a-zA-Z0-9 ]+ | [\s\S]
			ctl      :~ (\r\n?) | [\s\S]                         :: (c, cr) => markit.newNode('ctrl', (cr)?'\n':c)
			tag      :~ [^a-zA-Z0-9\s\u0080-\uffff]+
			symchar  :~ [^a-zA-Z0-9\x00-\x20]
		`;

		simpleProse.span = function(bmark, xs, emark) {     // span := sstart (nested/(!end nota))+ end
						                                    // => newNode('inlinenotation', xs, makePat(SPAN, bmark, emark))
			return newNode('inlinenotation', xs.flat(Infinity).join(''), makePat(SPAN, bmark, emark))
		} // simpleProse.span(bmark, xs, emark)

		var _qmarker	// save span begin and end (in closure)

		simpleProse.s_begin = function(mark) {              // sstart :~ %tag
			return _try(mark, closer(mark), this)

			function _try(mark, end_mark, parser) {
				if (applyLabel(makePat(SPAN, mark, end_mark), null) !== null) {
					_qmarker = {begin:mark, end:end_mark}
					return mark
				}
				// if a symbol of same length, fail to symbol rule
				if (applyLabel(makePat(SYM, mark), null) !== null)
					return null
				// else try one character shorter
				if (mark.length === 1)
					return null
				parser.pos--
				return _try(mark.substr(0, mark.length-1), end_mark.substr(1), parser)
			} // _try(mark, parser)
		} // simpleProse.s_begin(mark)

		simpleProse.n_begin = function(mark) {             // nstart :~ %tag
			const parser = this
			const begin_mark = _qmarker.begin
			if (begin_mark === _qmarker.end)  // quotes can't be nested
				return null
			if (mark.substr(0, begin_mark.length) === begin_mark) { // match => success
				parser.pos = parser.pos - (mark.length-begin_mark.length)
				return begin_mark
			} else // no match => fail; (parser.pos = parser.pos - mark.length)
				return null
		} // simpleProse.n_begin(mark)

		simpleProse.end_ = function(mark) {                // end :~ %tag
			return _try(mark, _qmarker.end, this)

			function _try(mark, end_mark, parser) {	// no recursive loop so could be folded back into outer function
				if (mark.substr(0, end_mark.length) === end_mark) {
					parser.pos = parser.pos - (mark.length - end_mark.length)
					return end_mark
				} else  // no match => fail; (parser.pos = parser.pos - mark.length)
					return null
			} // _try(mark, parser)
		} // simpleProse._end(mark)

		simpleProse.symbol = function(symbol) {           // symbol :~ %symchar [\\S]*
		                                                  // => newNode('inlinenotation', '', makePat(SYM, symbol))
			const label = _try(symbol, this)
			return (label) ? newNode('inlinenotation', '', label) : null

			function _try(symbol, parser) {
				const result = makePat(SYM, symbol)
				if (applyLabel(result, null) !== null)
					return result  // symbol match
				if (symbol.length === 1)
					return null
				// else try symbol one character shorter
				parser.pos--
				return _try(symbol.substr(0, symbol.length-1), parser)
			} // _try(symbol, parser)
		} // simpleProse.symbol(symbol)

		const _bracketsMap = {
			'(':')', ')':'(',
			'[':']', ']':'[',
			'<':'>', '>':'<',
			'{':'}', '}':'{'
		}

		function closer(begin) {
			var end = '';
			for (var i = begin.length - 1; i >= 0; i--)
				end += _bracketsMap[begin[i]] || begin[i];
			return end;
		}

		return (content) => simpleProse.parse(content)  // 'prose' transform

	} ()) // addBaseType('«prose»', ...


	core.addBaseType('prose', (content) =>                         // global 'prose' default is '«prose»'
		markit('«prose»', content)
	)

	core.addBaseType('text', (content) => content)                 // default for 'text' is just literal text

	core.addBaseType('ctrl', (content) => content)                 // 'ctrl' is just literal text
	
	core.addBaseType('inlinenotation', (content, label) =>         // escapes, spans and symbols - parmstring is the label pattern.
		applyLabel(label, content, 'prose')
	)


	/*
	 *  7. export Global API = markit() function with three sub-functions:
	 *      applyLabel:       function(label, content, defaultType)
	 *      setDefaultLingo:  function(lingo)
	 *      translate:        function(url)
	 */

	core.addBaseType = null  // initialization done, disable any further changes to set to base types.
	Object.freeze(core)      // and freeze core

	markit.applyLabel = core.applyLabel           // export sub-function to apply a label to content
	markit.newNode = core.newNode                 // export sub-function so transform parsers can create nodes
	markit.renderNodes = core.renderNodes         // export sub-function so transforms can render node lists
	markit.setDefaultLingo = core.setDefaultLingo // export sub-function for setting default lingo
	markit.translate = function(url) {            // export sub-function for translating contents of absolute url
		io.setLoadPath(url)            // set base for relative url's from parameter (should be absolute)
		core.useContext('0')           // reset context
		return markit('external', url) // return translated contents
	 } // translate(url)

	Object.freeze(markit)  // Global API, freeze it

	if (typeof module !== 'undefined' && typeof exports === 'object') {
		module.exports = markit;
	} else if (typeof define === 'function' && define.amd) {
		define(function () {
			return markit;
		});
	} else
		this.markit = markit;   // global translator markit(typeName, content)

}).call(function() {
	return this || (typeof window !== 'undefined' ? window : global);
} ());