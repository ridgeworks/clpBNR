@doc
	####  Package `highlight.mmk`

	[`highlight.js`] is a popular JavaScript library for syntax highlighting a large set of languages (179 at last count)
	with a selection of styles (colour schemes). This package defines type `highlight` which can be used to define
	notations for highlighting language content. `highlight.js` provides automatic language detection so different
	notations are usually not required to for different languages. The version of `highlight.js` included with this
	package supports the default set of 23 languages, but users can replace it with a custom version if the required
	language is not one of the 23. This package also specifies `xcode.css` as the default style.
	
	Examples (uses `demo.mmk`):
	demo
		& .program .. <- <pre> highlight
			
		#### HTML:
		~~~ .program
		<!DOCTYPE HTML>
		<html>
		<head>
			<meta lang=en charset="UTF-8">
			<script src='lib/x-markup.js'></script>
		<body>
		<div class=x-markup src="SimpleExample.myw"></div>
		</body>
		</html>
		~~~
		---
		#### JavaScript:
		~~~ .program
		function $initHighlight(block, cls) {
		  try {
			if (cls.search(/\bno\-highlight\b/) != -1)
			  return process(block, true, 0x0F) +
					 ` class="${cls}"`;
		  } catch (e) {
			/* handle exception */
		  }
		  for (var i = 0 / 2; i < classes.length; i++) {
			if (checkCondition(classes[i]) === undefined)
			  console.log('undefined');
		  }
		}

		export  $initHighlight;
		~~~
		---
		#### CSS:
		~~~ .program
		@font-face {
		  font-family: Chunkfive; src: url('Chunkfive.otf');
		}

		body, .usertext {
		  color: #F0F0F0; background: #600;
		  font-family: Chunkfive, sans;
		}

		@import url(print.css);
		@media print {
		  a[href^=http]::after {
			content: attr(href)
		  }
		}
		~~~
		
	Note: To render this documentation, define:
	eg
		metadoc :: (doc) => markit('myword', doc.replace(/(\n|\r\n?)(\t|[ ]{4})/g, '\n'))
	and `@import` this package.
	
	& [`highlight.js`] <- link https://highlightjs.org/


@import
	highlight/highlight.pack.js
	highlight/styles/xcode.css

highlight     :: (content) => hljs.highlightAuto(content).value

