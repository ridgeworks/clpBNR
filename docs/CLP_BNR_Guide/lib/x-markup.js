// -- x-markup: Browser interface to markit framework ---------------------------

/*	The MIT License (MIT)
 *
 *	Copyright (c) 2016,2017,2018 Rick Workman
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

// mark this script for the load handler

// if running as an HTML document script, add an id. This won't happen if running in an extension.
if (document.currentScript) document.currentScript.id = 'x-markitApp'

// add load event handler
window.addEventListener('load', function (ev) {  // Note: doesn't overwrite other handlers like "onload = function(ev) {..}
	const globals = window                         // some semblance of environment independence
	const target = ev.currentTarget.document
	const htmlScript = target.querySelector('script#x-markitApp')  // if running from HTML vs. extension
	const appScriptURL = (htmlScript) ? appURL(htmlScript.getAttribute('src')) : chrome.runtime.getURL("lib/x-markup.js")
	const appName = (appScriptURL.lastIndexOf('/') === -1) ? appScriptURL : appScriptURL.substring(appScriptURL.lastIndexOf('/') + 1)
	const versionString = appName + ' Version: 1.2'
	//const mimeType = 'text/x-markup.'              // in practice: text/x-markup.transformName
	const workerName = 'markit.js'
	const lingoName = 'x-markup.mmk'
	
	function appURL(scriptURL) {    // convert relative URL to absolute
		return /^\/|:\/\//.test(scriptURL)  // starts with '/' or contains '://'
			? scriptURL
			: location.href.substring(0, location.href.lastIndexOf('/') + 1) + scriptURL
	}
	
	var MarkIt = null  // markit Worker - newWorker() will initialize it
	var initQueue = [] // holds window messages until init complete. Probably a corner case but better to be safe.

	const errorMessage = function (errorLabel) {
		return function(msgComponents) {
			return errorLabel + msgComponents.join(' ')
		}
	} (['***', appName, 'error:'].join(' '))

	function logError(err) {
		console.error(err.message)
		const preElement = document.createElement('pre')
		preElement.innerHTML = ['<mark style="color:blue">',err.message,'</mark>'].join('')
		document.body.appendChild(preElement)
	} // logError(err)
	
	// handle load event
	console.log(navigator.appCodeName, navigator.appVersion)
	console.log(versionString)

	// event handler for window messages to request translation
	globals.addEventListener('message', function (event) {
		if (event.source === window) try {    // only local messages supported
			if (Array.isArray(initQueue)) {   // still initializing?
				initQueue.push(event.data)
			} else {
				if (event.data.type) {
					post(event.data.type, target.body.querySelector(event.data.selector))  // post request to markit
				}
			}
		} catch (err) {
			logError(new Error(errorMessage(['handling message', JSON.stringify(event.data), 'error:', err])))
		}
	})

	// Promise based initialization
	newWorker(appScriptURL.replace(appName, workerName))  // init Worker
		.then(getLingo)                   // then fetch the default lingo
		.then(setLingo)                   // then get the Worker to set the lingo
		.then(processScripts)             // then process the content
		.catch(logError)                  // catch any errors in the process

	async function newWorker(workerURL) {
		try {
			return initWorker(new globals.Worker(workerURL))
		} catch (err) {
			if (err.code === 18/*DOMException.SECURITY_ERR*/) { // fudge for extensions loading a worker
				const response = await fetch(workerURL)
				if (response.ok) {
					const extWorkerURL =
						URL.createObjectURL(new Blob(['_extensionHref="', workerURL, '";\n', await response.text()], {type: 'text/javascript'}))
					return initWorker(new globals.Worker(extWorkerURL))
				} else {
					throw new Error(errorMessage([workerURL, response.status, '(', response.statusText, ')']))
				}
			}
		}

		function initWorker (worker) {
			worker.onmessage = function (content) {
				updateDOM(content.data[0], content.data[1])
			} // worker.onmessage
			worker.onerror = function (err) { // if this happens, it's a bug (uncaught exception in Worker?)
				logError(new Error(errorMessage(['Worker', err.message])))
			} // worker.onerror
			worker.nxtID = 1
			return worker
		} // initWorker (worker)
	} // newWorker(url)

	async function getLingo(worker) {  // fetch default lingo
		MarkIt = worker  // initialize shared var
		const lingoURL = appScriptURL.replace(appName, lingoName)
		const response = await fetch(lingoURL)
		if (response.status === 200 || response.status === 0) {
			return response.text()
		} else {
			throw new Error(errorMessage([lingoURL, response.status, '(', response.statusText, ')']))
		}
	} // getLingo(worker)

	async function setLingo(lingo) {  // send default lingo to Worker
		MarkIt.postMessage([null, 'metamark', lingo, '0', appScriptURL.replace(appName, lingoName)])
		return true  // Worker messages do the rest.
	} // setLingo(lingo)

	// Search for DOM content to translate
	function processScripts() {
		const myClass = 'x-markup'
		if (target) {
			console.log('Document URL='+location.href)
			if (htmlScript) {  // running from htmlContent rather than extension
				if (location.search) { // check if query parameter has src='... .myw'
					var srcURL = location.search.match(/\?.*src=([^&]+)/)  //find a src key in query string and extract URL
					if (srcURL) {  // prepend a <div class=x-markup src=srcURL> element to the body
						srcURL = srcURL[1]
						if (srcURL.substr(-4) !== '.myw') srcURL += '.myw'
						const newdiv = document.createElement('div')
						newdiv.setAttribute('class', myClass)
						newdiv.setAttribute('src', srcURL)
						target.body.insertBefore(newdiv, target.body.firstChild)
					}
				}
				target.body.querySelectorAll("div." + myClass).forEach(
					function (div) {
						var srcURL = div.getAttribute('src')
						if (srcURL === '?') {  // if URL===?, use document name with .myw prefix.
							const docURL = document.documentURI
							srcURL = docURL.substring(0, docURL.lastIndexOf('.')) + '.myw'
							if (document.title.length === 0) {
								document.title = srcURL.substring(srcURL.lastIndexOf('/') + 1)
							}
						}
						if (srcURL) {  // if no URL, don't post it (silent failure)
							div.textContent = srcURL
							post('external', div, `Rendering ${srcURL} ...`)
						}
					}
				)
				if ((target.body.childElementCount === 0))  // nothing in <body> , stick in an error message
					target.body.innerHTML = '<pre><mark style="color:blue">No MyWord content found for this page!</mark></pre>'
			} else {  // running from extension - use contents of <pre> as myword source
				const newdiv = document.createElement('div')
				newdiv.setAttribute('class', myClass)
				const sourceElement = target.body.querySelector('pre')
				newdiv.textContent = sourceElement.textContent
				document.body.replaceChild(newdiv, sourceElement)
				post('myword', newdiv)
			}
			// process pending window message queue
			initQueue.forEach(function(msg) {
				post(msg.type, target.body.querySelector(msg.selector))
			})
			initQueue = null  // subsequent window messages go directly to post()
		}
	} // processScripts()

	// post message to MarkIt to translate an element's content according to the type
	// element's contents set to optional statusMsg during rendering
	function post(type, element, statusMsg) {
		if (type && element) {
			element.style.visibility = 'hidden'  // hide element while rewriting it
			if (!element.getAttribute('id')) {   // if element doesn't have an ID, manufacture one
				element.setAttribute('id', 'FWmsg' + MarkIt.nxtID++)
			}
			element.style.margin = 'inherit'     // inherit margins
			try {
				// document base is just origin and pathname, any fragment or query is dropped
				const origin = (document.location.origin === 'null') ? 'file://' : document.location.origin // for Firefox 'null' origin value
				MarkIt.postMessage([element.getAttribute('id'), type, element.textContent, contextID(element), origin + document.location.pathname])
				if (statusMsg) {
					element.innerHTML = statusMsg
					element.style.visibility = 'visible'
				}
			} catch (err) {
				if (element) element.style.visibility = 'visible'  // make element visible again
				// leave element alone, error message in console
				console.error(errorMessage([err.message, 'posting', type, 'content to', document]))
			}
		}

		function contextID(elem) {    // look up a contextID value in the element or one of its ancestors.
			if (elem === null)
				return '0'
			else {
				const id = elem.getAttribute('data-context')
				return (id) ? id : ((elem.tagName.toLowerCase() === 'body') ? '0' : contextID(elem.parentNode))
			}
		} // contextID(elem)
	} // post(type,element)

	// update an element in the DOM with new content from the Worker, returns modified element
	function updateDOM(elemID, content) {
		// Note special case - elemID == null, means loading x-markup.mmk
		const element = (elemID) ? document.getElementById(elemID) : document.body
		if (element) {
			if (typeof content === 'string') {
				try {
					if (element.tagName.toLowerCase() === 'body') {  // reply from x-markup.mmk translation
						const temp = document.createElement('div')     // will be garbage collected
						temp.style.margin = 'inherit'   // inherit margins
						temp.innerHTML = content
						const tempChildren = temp.children             //Note: live collection
						const bodyFirst = element.firstChild
						while (tempChildren.length > 0)
							element.insertBefore(tempChildren[ 0 ], bodyFirst)
						return element
					} else {
						element.innerHTML = content
						element.style.visibility = 'visible'           // have to render before adjusting size
						const iframe = document.defaultView.frameElement
						if (iframe) {
							// Use Mutation observer to update iframe height.
							const iframeObserver = new MutationObserver(function (mutations, observer) {
								observer.iframe.style.height = (observer.iframe.contentDocument.body.clientHeight) + 'px'
							})
							iframeObserver.iframe = iframe
							iframeObserver.observe(iframe.contentDocument.body, { childList: true, subtree: true, attributes: true })
							window.addEventListener('resize', function (ev) {
								// Update a body attribute to trigger MutationObserver
								document.body.setAttribute('re-size', '')
							})
						}
						const scripts = element.getElementsByTagName('script')  // have to clone & replace scripts to get them executed
						var script, newscript
						for (var s = 0; s < scripts.length; s++) {
							script = scripts[ s ]
							newscript = document.createElement('script')
							newscript.innerHTML = script.innerHTML
							for (var ai = 0; ai < script.attributes.length; ai++) {
								newscript.setAttribute(script.attributes[ ai ].name, script.attributes[ ai ].value)
							} // for
							script.parentElement.replaceChild(newscript, script)
						} // for
					}
					dispatchUpdate(document, element)                  // invoke listeners for update
				} catch (err) {
					element.style.visibility = 'visible'  // something failed, just make element visible again
					console.error(errorMessage([ err.message, 'updating', element ]))
				}
			} else element.style.visibility = 'visible'            // no new content, make it visible
		}
		return element
	} // updateDOM(elemID, content)


	// Browser feature status (non-essential info)
	function noArrow() {
		var arrow = true
		try { eval('(() => true)') } catch (err) { arrow = false }  // just a test, not used
		return !arrow
	} // noArrow()
	console.log([ 'Arrow functions are ', noArrow() ? 'NOT ' : '', 'supported in this browser.' ].join(''))

	const noCustomElements = (!globals.customElements)
	console.log([ 'Custom Elements(V1) are ', noCustomElements ? 'NOT ' : '', 'supported in this browser.' ].join(''))
	//if (!noCustomElements && customElements.polyfilled)
	//	console.log('\tvia polyfill.')

	/* ******************  Start of "feature" listeners  ********************* */

	var listeners = [] // listener events dispatched to listeners whenever MarkIt returns new HTML content

	function addListener(listener) {
		if (typeof listener === 'function') {
		if (listeners.indexOf(listener) === -1)
				listeners.push(listener)  // new listener, add it
		} else console.error(errorMessage(['Invalid listener:', listener]))
	} // addListener(listener)

	function removeListener(listener) {
		const lix = listeners.indexOf(listener)
		if (lix >= 0)
			listeners.splice(lix, 1)
	} // removeListener(listener)

	function dispatchUpdate(document, element) {  // called from updateDOM()
		listeners.forEach(function (listener) {listener.call(null, document, element)})
	} // dispatchUpdate(document, element)


	// Math plug-in : use MathJax if loaded
	const hasMathML = function() {  // returns true if platform has native MathML support
		var hasMML = false
		if (document.createElement) {
			var div = document.createElement('div')
			div.style.position = 'absolute'
			div.style.top = div.style.left = 0
			div.style.visibility = 'hidden'
			div.style.width = div.style.height = 'auto'
			div.style.fontFamily = 'serif'
			div.style.lineheight = 'normal'
			div.innerHTML = '<math><mfrac><mi>xx</mi><mi>yy</mi></mfrac></math>'
			document.body.appendChild(div)
			hasMML = (div.offsetHeight > div.offsetWidth) // proper fraction rendering has height > width
			document.body.removeChild(div)
		}
		return hasMML
	} ()

	//var noMML = !hasMathML()  // not used in this version
	console.log(['MML is ', hasMathML ? '' : 'NOT ', 'supported in this browser.'].join(''))
	if (/* noMML && */ (typeof globals.MathJax !== 'undefined')) { // if (MathJax) add feature listener
		addListener(function (document, element) {
			globals.MathJax.Hub.Queue([ 'Typeset', globals.MathJax.Hub, element ])
		})
	}
	
	if (/* noMML && */ (typeof globals.Typeset !== 'undefined')) { // if (MathJax3) add feature listener
		addListener(function (document, element) {
			var mathElements = element.querySelectorAll('math')  // get all math elements in element
			mathElements.forEach((mathElement) => {
				try {
					mathElement.parentNode.replaceChild(Typeset(mathElement.outerHTML), mathElement)
				} catch(err) {
					console.error("MathJax Typeset error: "+err.message)
				}
			})
		})
	}
	


	/* Polyfill for scoped styles - plagerized from (https://github.com/thomaspark/scoper)

	 Copyright (c) 2015 Thomas Park

	 Permission is hereby granted, free of charge, to any person obtaining a copy
	 of this software and associated documentation files (the "Software"), to deal
	 in the Software without restriction, including without limitation the rights
	 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
	 copies of the Software, and to permit persons to whom the Software is
	 furnished to do so, subject to the following conditions:

	 The above copyright notice and this permission notice shall be included in all
	 copies or substantial portions of the Software.

	 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
	 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
	 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
	 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
	 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
	 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
	 SOFTWARE.
	 */
	function scopeIt (document, element) {
		const idPrefix = 'scoper-'
		const styles = element.querySelectorAll('style[scoped]')
		if (styles.length > 0) {
			if (!(MarkIt.scopeID)) MarkIt.scopeID = 0
			// Need to sort list to ensure outer styles do not override inner styles
			var csses = Array.from(styles).sort((a, b) =>
					(a.parentNode === b.parentNode)
						? 0                                               // at same level, preserve order
						: (b.parentNode.contains(a.parentNode) ? 1 : -1)  // if b outer, switch order
				).map(function(style) {
					if (style.innerHTML) {
						const parent = style.parentNode
						const grandparent = parent.parentNode
						// don't process any immediate decendants of body element (shouldn't wrap body element)
						if (parent.tagName.toLowerCase() !== 'body') {
							var scopeID
							if (grandparent.tagName.toLowerCase() === 'span' &&
								grandparent.id.substr(0, idPrefix.length) === idPrefix) {  // scope already there, use it
								scopeID = grandparent.id
							} else {                                                       // create a scope
								scopeID = idPrefix + (MarkIt.scopeID++)
								const wrapper = document.createElement('span')
								wrapper.id = scopeID
								grandparent.replaceChild(wrapper, parent)
								wrapper.appendChild(parent)
							}
							parent.removeChild(style)
							return scoper(style.innerHTML, '#' + scopeID)
						}
					}
				}).join('')
			const newstyle = document.createElement('style')
			if (newstyle.styleSheet) {
				newstyle.styleSheet.cssText = csses
			} else {
				newstyle.appendChild(document.createTextNode(csses))
			}
			(document.head || document.getElementsByTagName('head')[0]).appendChild(newstyle)
		}
		
		function scoper (css, prefix) {
			return css.replace(/([^\r\n,{}]+)(,(?=[^}]*{)|\s*{)/g, function (g0, g1, g2) {
				if (g1.match(/^\s*(@media|@keyframes|to|from)/)) {
					return g1 + g2
				}
				g1 = g1.replace(/^(\s*)/, '$1' + prefix + ' ')
				return g1 + g2
			})
		} // scoper(css, prefix)
	} // scopeIt(document, element)

	const noscoped = !('scoped' in document.createElement('style'))
	console.log(['Scoped styles are ', noscoped ? 'NOT ' : '', 'supported in this browser.'].join(''))
	if (noscoped) addListener(scopeIt)  // add scopeIt to feature listeners


	// Document feature to mark local links (href=#...) which are not defined
	function markBadLocalLinks (document, element) {
		element.querySelectorAll('a[href^="#"]').forEach(function (localRef) {
			if (!document.getElementById(localRef.getAttribute('href').substring(1))) {
				localRef.innerHTML = "<span class=Undefined>" + localRef.innerHTML + "</span>"
				console.error(errorMessage(['Undefined local link in', localRef.outerHTML]))
			}
		})
	} // markBadLocalLinks (document, element)

	addListener(markBadLocalLinks)


	// Go to fragment, but only do it once
	function gotoFragment (document) {
		document.getElementById(location.hash.substr(1)).scrollIntoView(true)
		removeListener(gotoFragment)
	} // gotoFragment (document)
	
	// if fragment in URL, go there after loading
	if (location.hash) addListener(gotoFragment)


}) // window.addEventListener(...