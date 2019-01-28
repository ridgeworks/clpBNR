@doc
	***** Default Lingo *****
	Type definitions required for basic HTML generation

text        :: (content) => content.replace(/&/g,'&amp;').replace(/</g,'&lt;')

ctrl        :: (ctl) => {
	             switch (ctl) {
	               case '\n' : return '<span class=newline>\n</span>'
	               case '\t' : return '<span class=tab>\t</span>'
	               default   : return `<span class=my_ctl data-code='${ctl.charCodeAt(0).toString()}'>\ufffd</span>`
	             }
	           }

insetblock  :: (content, codeclass) =>
	                  `<pre><code class=${codeclass ? codeclass : 'my_text'}>${markit('text', content)}</code></pre>`

fencedblock :: (content, infostring) =>
	             ( (label = infostring.match(/(\S*)/)[1]) =>
	                 (markit.applyLabel(label + ' ..', null) !== null)
	                   ? markit('labeledblock', content, label + ' ..')
	                   : markit('insetblock', content, (label ? 'language-' + label : ''))
	             ) ()

paragraph   :: (content) => `<p class=my_p>${markit('prose', content)}</p>`

blankline   :: (_) => '<div class=my_blank>&nbsp;</div>'

scope       :: (content, context) =>
	             (context) ? `<span class=myword data-context=${context}>${content}</span>` : content

errorString :: (content) => {
	             if (console) console.error('markit: ' + content)
	             return `<pre><mark style='color:blue'>*** Error *** ${markit('text', content)}</mark></pre>`
	           }

metajs      :: (javascript) => `<script type=application/javascript>${javascript}</script>`
metacss     :: (css) => `<style scoped>${css}</style>`


@doc
	document level CSS rules

@css
	body {tab-size:4; -moz-tab-size:4}   /* default tab size=4 spaces; inherited by all body content */
	span.newline {white-space:pre}       /* newline is a hard line break */
	p.my_p {margin:0}                    /* paragraph margin=0 (overrides user agent spacing) */
	div.my_blank {visibility:hidden}     /* blankline is spacing only, no visibles */


@doc
	Types for treating parmstring in label defintions as the content for symbols
	
	`viz` treats parmstring as `prose`
	`is` treats parmstring as raw text

viz         :: (_, parmstring) => markit('prose', parmstring)
is          :: (_, parmstring) => parmstring


@doc	`{ .. }` span notation (with alternative) for labeled inline content

{ .. }      <- inline { }
{( .. )}    <- inline {( )}

inline      :: (content, brackets) => ((parsed = content.match(/(\s*)(\S+)\s*([\S\s]*)/), br = brackets.split(' ')) =>
	              (!parsed[1] && (markit.applyLabel(parsed[2]+' ..', null) !== null))
	                ? markit.applyLabel(parsed[2]+' ..', parsed[3], 'prose')
	                : [br[0], markit('prose', parsed[0]), br[1]].join('')
	            ) ()


@doc	`[ .. ]` span notation for placeholders (references to label defintions)

[ .. ]      <- asdefined
asdefined   :: (contents) => ((defined = markit.applyLabel('['+contents.trim()+']', contents, 'prose')) =>
	             defined
	               ? defined
	               : `<span class=Undefined>[${markit('text', contents)}]</span>`
	           ) ()


@doc
	`< .. >` span notation for hyperlinks, content is URL or email address, or notation can be literal `prose`
	(Note: `link` type also used in placeholder defintions which supply the URL in the parmstring.)

< .. >      <- link
link        :: (contents, spec) =>
	              ((attrs=spec?spec.match(/\s*(\S+)([\s\S]*)/):null) =>
	                attrs
	                  ? `<a href='${attrs[1]}' ${attrs[2].trim()}>${markit('prose',contents)}</a>`
	                  : ((/[\w!#$%&‘*+–/=?^`.{|}~]+@[\w-.]+/.test(contents.trim()))) 
	                    ? `<a href='mailto:${contents.trim()}'>${contents}</a>`
	                    : ((/(?:(?:^[a-z](?:[-a-z0-9+.])*:\/\/)|(?:^[\/]?[^\s\/]+[\/.][^\s]+)|(?:#))\S+$/.test(contents.trim())))
	                      ? `<a href='${contents.trim()}'>${contents}</a>`
	                      : ['&lt;', markit('prose', contents), '>'].join('')
	              ) ()


@doc
	`#id ..` block notation for internal link targets, which are hidden by default.
	`id` attribute value is the first word of the content, any remaining content is treated as `prose`.
	

#id ..       <- target
target       :~ (\S+\s*)([\S\s]*) :: (_, id, content) =>
	                   `<span class=target id='${id.trim()}'>${markit('text', id)}</span>${markit('prose', content)}`

@css
	span.target {visibility:hidden; height:1px; width:1px; position:absolute;}


@doc	`image` type for use with placeholders, e.g., `[gopher] <- image images/gopher.png`

image        :: (contents, spec) =>
	               ((attrs=spec?spec.match(/\s*(\S+)([\s\S]*)/):[spec,'']) =>
		   `<img src='${attrs[1]?attrs[1]:contents.trim()}'${attrs[2]} alt='${markit('text',contents)}'/>`
		           ) ()


@doc
	Common Light-weight Markup:
	-  block notations for headers (with id's) and block quote
	-  span notation for escaping inline notations.
	-  span notations for simple markup:`italics`, `bold` (with `alternatives), and `code`.
	-  span notation for typograhical double quotes
	-  symbols for horizontal rule and apostrophe

# ..         <- header 1
## ..        <- header 2
### ..       <- header 3
#### ..      <- header 4
##### ..     <- header 5
###### ..    <- header 6

header       :: (c, level) =>
	              `<h${level} class=my_h${level} id='toc${level}${c.trim().replace(/[^\w$-@.&!*(),]/g, '_')}'>${markit('prose', c)}</h${level}>`

> ..         <- <blockquote class=my_blockquote> blockquote

// if no content in a blockquote, treat as a blank line (for MD compatability)
blockquote   :: (content) => markit((content) ? 'myword' : 'blankline', content)

// inlines including span alternatives. Note class attribute for more refined style rules if necessary
//		\ .. \                : escape
//		` .. `                : code
//		* .. * and _ .. _     : emphasis
//		** .. ** and __ .. __ : strong
//		" .. "                : quotes

\ .. \       <- <span class=my_text> text
\( .. )\     <- <span class=my_text> text

` .. `       <- <code class=my_text> text
`` .. ``     <- <code class=my_text> text
`( .. )`     <- <code class=my_text> text

* .. *       <- <em>
*( .. )*     <- <em>
_ .. _       <- <em>
_( .. )_     <- <em>

** .. **     <- <strong>
**( .. )**   <- <strong>
__ .. __     <- <strong>
__( .. )__   <- <strong>

" .. "       <- <q class=my_dquo>
"( .. )"     <- <q class=my_dquo>

--- ..       <- <hr class='my_hr'/>
'            <- &rsquo;

@css
	h1.my_h1, h2.my_h2, h3.my_h3, h4.my_h4, h5.my_h5, h6.my_h6 {margin:0}
	blockquote.my_blockquote {margin:0 40px}
	q.my_dquo {quotes: "\201c" "\201d"}
	.my_text {white-space:pre}


@doc
	Lists:
	Alternative block notations for list items: `*` or `+` or `-`
	`*..` block notation for unordered list
	Several block notations for ordered list for numbers, letters, roman numerals etc.

* ..         <- <div class=my_listitem>
+ ..         <- <div class=my_listitem>
- ..         <- <div class=my_listitem>
*.. ..       <- <ul class=my_list style="list-style-type:disc">
1.. ..       <- orderedlist decimal
01.. ..      <- orderedlist decimal-leading-zero
i.. ..       <- orderedlist lower-roman
I.. ..       <- orderedlist upper-roman
A.. ..       <- orderedlist upper-latin
a.. ..       <- orderedlist lower-latin

orderedlist  :: (content, type) =>
	              `<ol class=my_list style="list-style-type:${type}">${markit('myword',content)}</ol>`

@css
	.my_list {margin:0px}
	.my_list div.my_listitem {margin-left:0px}
	div.my_listitem {display:list-item; margin-left:40px}
	div.my_listitem > div.my_listitem {list-style-type:circle; margin-left:40px}
	div.my_listitem > div.my_listitem > div.my_listitem {list-style-type:square}


@doc
	`@include` block notation for including external content via a whitespace separated URL list.
	It applies core type `external` to each URL in the list.
	`myw` and `txt` types defined for file suffixes used with `@include`

@include .. <- reflist

reflist     :: (list) =>
	              list.trim().split(/\s+/).map((ref) => 
	                 markit('external', ref)
	              ).join('')
	              
// file types, including `md` for Markdown
myw         :: (content) => markit('myword', content)
txt         :: (content) => `<pre class=txtInclude>${markit('text', content)}</pre>`
md          :: (content) => new commonmark.HtmlRenderer().render(new commonmark.Parser().parse(content))
@import commonmark.min.js
