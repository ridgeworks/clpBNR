@doc .myw
	####  Package `demo.mmk`
	This package provides useful block notations for software documentation: examples and side-by-side demos. It defines four `block` notations: `eg ..`, `demoS ..`, `demo ..`, and `demoH ..`. Here are examples of each:
	#####	Example code block
	A code (or other) example can be written using the `eg` block label. It wraps the literal content in a `<div class='eg'>` element and applies some simple style rules.
	eg
		###  A Header
	#####	Static Demo
	The `demoS` block notation splits generates a table with two columns displaying `myword` source on the right and the rendered version on the left. For example:
	demoS
		###  A Header
		This content is contained in a static `demoS` block.
	#####	Interactive Demo
	The `demo` block notation is similar to `demoS` except the user can modify the `myword` source on the left side of the document. When the source is in focus, i.e., editable, the background colour changes to light yellow.
	demo
		*Modify me!*
		This content is contained in an interactive `demo` block.
	#####	Interactive Demo with HTML
	The `demoH` block notation further enhances `demo` to add the generated HTML under the rendered source along with a button under the source itself to toggle the HTML display. The initial state is HTML hidden.
	demoH
		*Modify me!*
		This content is contained in an interactive `demoH` block with a button to toggle the display of the generated HTML code.

	The `eg` and `demoS` defintions are fairly simple, but make heavy use of CSS to control presentation:
	eg
		eg ..        <- <div class='eg'> text

		demoS ..     <- <div class='demo'> demo

		demo         :: (content) =>
			              `<div class='A1'><div class=hscroll>${markit('text', content)}</div></div>
			               <div class='B1'>${markit('myword', content)}</div>
			              `
		@css
			div.eg {overflow-x:auto;}

			div.demo {
				display:table; table-layout:fixed; width:100%;
				border-spacing:5pt 0pt;
			}

			div.demo {display:table-row;}

			div.demo div.A1, div.demo div.B1 {display:table-cell;}

			div.eg, div.demo div.A1 {
				padding-left:10pt; padding-right:10pt; padding-top:5pt; padding-bottom:5pt;
				white-space:pre; font-family:monospace; background:whitesmoke;
			}

			div.demo div.A1 {width:50%; vertical-align:top;}

			div.demo div.A1 div.hscroll {overflow-x:auto;}

			div.demo div.B1 {vertical-align:top;}

	The interactive variants of `div.demo` have much the same structure and  CSS rules but require two custom elements to implement dynamic updating, i.e., when the source content (the left hand side) is changed the MyWord Worker must be used to translate the modified content; the result is then used to update the rendered content (the right hand side).
	
	The source content is an instance of the `<myword-editable>` custom elmement which is bound to JavaScript class `MyWordEditable`. The class code is responsible for setting the `contentEditable` attribute to `true` and for overriding standard browser behaviour for the `Tab` and `Enter` keys.
	
	The rendered content is contained in an instance of `<myword-sink>` and implemented via the `MyWordSink` class. The `data-source` attribute of this element is a selector identifying an element to be monitored for changes (via a `MutationObserver`). If multiple elments match the selector pattern, a nearest neighbour algorithm is used to find the closest one. In this case the `<myword-editable>` element and the `<myword-sink>` element share a common ancestor (`div.demo`) and so the desired relationship is guaranteed. 
	
	When the `<myword-sink>` receives notification of a change, the current contents of the element are replaced by the contents of the `<myword-editable>` element and a message is sent via the `window` messaging interface to request that translation of `<myword-sink>` element be started. When translation finishes the newly rendered content replaces the current content.
	
	&
		// local def of ### and ##### so it doesn't end up in table of contents
		### ..   <- <h3> prose
		##### .. <- <h5> prose

eg ..        <- <div class='eg'> text


demoS ..     <- <div class='demo'> demo

demo         :: (content) =>
	              `<div class='A1'><div class=hscroll>${markit('text', content)}</div></div>
	               <div class='B1'>${markit('myword', content)}</div>
	              `


demo ..      <- <div class='demo'> demoI

demoI        :: (content) =>
	             `<div class='A1'><div class=hscroll><myword-editable>${markit('text', content)}</myword-editable></div></div>
	              <div class='B1'><myword-sink data-source='.A1' data-type=myword>${markit('myword', content)}</myword-sink></div>
	             `


demoH ..     <- <div class='demo'> demoIH

demoIH       :: (content) => (
	              (source = content, html = markit('myword', content)) =>
	                `<div class=trow>
	                  <div class='A1'><div class=hscroll><myword-editable>${markit('text', source)}</myword-editable></div></div>
	                  <div class='B1'><myword-sink data-source='.A1' data-type=myword>${html}</myword-sink></div>
	                </div>
	                <div class=trow>
	                  <div style='display:table-cell; vertical-align:top'><button onclick='((toHide) => toHide.hidden = !toHide.hidden) (this.parentElement.nextElementSibling)'>Toggle HTML Display</button></div>
	                  <div class='A3' hidden><div><myword-sink data-source='.B1>myword-sink'>${markit('text', html)}</myword-sink></div></div>
	                </div>`
	            ) ()


// CSS to control appearance
@css
	div.eg {overflow-x:auto;}

	div.demo {
		display:table; table-layout:fixed; width:100%;
		border-spacing:5pt 0pt;
	}
	
	div.demo div.trow {display:table-row;}
	
	div.demo div.A1, div.demo div.B1 {display:table-cell;}

	div.eg, div.demo div.A1 {
		padding-left:10pt; padding-right:10pt; padding-top:5pt; padding-bottom:5pt;
		white-space:pre; font-family:monospace; background:whitesmoke;
	}

	div.demo div.A1 {width:50%; vertical-align:top;}

	div.demo div.A1 div.hscroll {overflow-x:auto;}

	div.demo div.B1 {vertical-align:top;}

	div.demo div.A3 {
		vertical-align:top;
		padding-left:10pt; padding-right:10pt;
		white-space:pre; font-family:monospace; background:whitesmoke;
	}

	div.demo div.A3 div {overflow-x:auto;}

	myword-editable {display:block; word-wrap:normal; overflow-x:inherit;}
	myword-editable:focus {outline:none; background:lightyellow;}

// Javascript to implement custom elements (v1) for interactive demos.
@javascript
	( () => {
		// <myword-editable> - editable element permitting tab input
		class MyWordEditable extends HTMLElement {
		
			constructor() {
				super()
				this.contentEditable = true
				this.keyHandler = this.keydown.bind(this)  // initialize event handler bound to this object
			} // constructor()
			
			connectedCallback() {
				this.addEventListener('keydown', this.keyHandler)
			} // connectedCallback()
			
			disconnectedCallback() {
				this.removeEventListener('keydown', this.keyHandler)
			} // disconnectedCallback()
			
			keydown(event) {
				//console.log('keydown='+event.key)
				// Safari, Chrome issue:
				//   auto scroll doesn't happen if 'insertText'ing off the right, corrects on any other key
				if (!event.defaultPrevented) {  // Safari, Chrome issue: only insert if not defaultPrevented already
					if (event.key === 'Tab' || event.keyCode == 9 || event.which == 9) {
						document.execCommand('insertText', false, '\t')
						event.preventDefault()
					} else if (event.key === 'Enter' || event.keyCode == 13 || event.which == 13) {
						// Work around for FireFox changing leading tab to a space
						try {
							document.execCommand('insertText', false, '\n')
						} catch (err) { /*console.debug(err)*/ }  // first time on Firefox, ignore?
						this.scrollLeft = 0  // for Safari, Chrome auto-scroll issue
						event.preventDefault()
					}
				}
				return false    // don't lose focus
			} // keyHandler(event)
								
		} // MyWordEditable

		if (!customElements.get('myword-editable'))
			customElements.define('myword-editable', MyWordEditable)

		// <myword-sink> - monitor a source for change and transform source.contents to this.contents
		class MyWordSink extends HTMLElement {
		
			constructor() {
				super()
				this.sourceObserver = new MutationObserver((mutations, observer) => {
					if (observer.type) {
						observer.sink.textContent = observer.source.innerText || observer.source.textContent
						window.postMessage({type: observer.type, selector: this.tagName.toLowerCase()+'#'+this.id}, '*')
					} else {
						observer.sink.textContent = observer.source.innerHTML // no type, display raw HTML as text
					}
				}) // sourceObserver
			} // constructor()
			
			connectedCallback() {
				var findClosest = (parentElem, selector) => {
					// find the closest relative matching selector
					var closest = null
					if (parentElem) {
						closest = parentElem.querySelector(selector)
						if (!closest) closest = findClosest(parentElem.parentElement, selector)
					}
					return closest
				} // findClosest(parentElem, selector)
				if (!this.id) this.id = 'sink' + Math.round(Math.random()*1000000)  // make sure element has an id
				var sourceSelector = this.getAttribute('data-source')
				var type = this.getAttribute('data-type')
				if (sourceSelector) {
					var source = findClosest(this, sourceSelector.trim())
					if (source) {
						this.sourceObserver.source = source
						this.sourceObserver.sink = this
						this.sourceObserver.type = type ? type.trim() : null
						this.sourceObserver.observe(source, {subtree: true, childList:true, characterData: true, attributes:true})
						source.setAttribute('my-init', 'true')  // trigger an event
					} else {
						var errorInfo = "No source found in &lt;myword-sink> using selector " + sourceSelector
						console.error(errorInfo)
						this.innerHTML = ["<pre><mark style='color:blue'>\n*** Error *** ", errorInfo, "\n</mark></pre>"].join('')
					}
				}
			} // connectedCallback()
			
			disconnectedCallback() {
				this.sourceObserver.disconnect()
			} // disconnectedCallback()
			
		} // MyWordSink

		if (!customElements.get('myword-sink'))
			customElements.define('myword-sink', MyWordSink)

	}) ()
