# 2. Lexical and Low Level Grammar
Dafny uses the Coco/R lexer and parser generator for its lexer and parser
(<http://www.ssw.uni-linz.ac.at/Research/Projects/Coco>)[@Linz:Coco].
The Dafny input file to Coco/R is the `Dafny.atg` file in the source tree.
A Coco/R input file consists of code written in the target language
(C\# for the `dafny` tool) intermixed with these special sections:

0. The [Characters section](#sec-character-classes)
    which defines classes of characters that are used
   in defining the lexer.
1. The [Tokens section](#sec-tokens) which defines the lexical tokens.
2. The [Productions section](#sec-grammar)
 which defines the grammar. The grammar productions
are distributed in the later parts of this document in the places where
those constructs are explained.

The grammar presented in this document was derived from the `Dafny.atg`
file but has been simplified by removing details that, though needed by
the parser, are not needed to understand the grammar. In particular, the
following transformations have been performed.

* The semantics actions, enclosed by "(." and ".)", were removed.
* There are some elements in the grammar used for error recovery
  ("SYNC"). These were removed.
* There are some elements in the grammar for resolving conflicts
  ("IF(b)"). These have been removed.
* Some comments related to Coco/R parsing details have been removed.
* A Coco/R grammar is an attributed grammar where the attributes enable
  the productions to have input and output parameters. These attributes
  were removed except that boolean input parameters that affect
  the parsing are kept.
  * In our representation we represent these
    in a definition by giving the names of the parameters following
    the non-terminal name. For example `entity1(allowsX)`.
  * In the case of uses of the parameter, the common case is that the
    parameter is just passed to a lower-level non-terminal. In that
    case we just give the name, e.g. `entity2(allowsX)`.
  * If we want to give an explicit value to a parameter, we specify it in
    a keyword notation like this: `entity2(allowsX: true)`.
  * In some cases the value to be passed depends on the grammatical context.
    In such cases we give a description of the conditions under which the
    parameter is true, enclosed in parenthesis. For example:

      `FunctionSignatureOrEllipsis_(allowGhostKeyword: ("method" present))`

    means that the `allowGhostKeyword` parameter is true if the
    "method" keyword was given in the associated ``FunctionDecl``.
  * Where a parameter affects the parsing of a non-terminal we will
    explain the effect of the parameter.


The names of character sets and tokens start with a lower case
letter; the names of grammar non-terminals start with
an upper-case letter.

The grammar uses Extended BNF notation. See the [Coco/R Referenced
manual](http://www.ssw.uni-linz.ac.at/Research/Projects/Coco/Doc/UserManual.pdf)
for details. In summary:

* identifiers starting with a lower case letter denote
terminal symbols
* identifiers starting with an upper case letter denote nonterminal
symbols
* strings (a sequence of characters enclosed by double quote characters)
denote the sequence of enclosed characters
* `=` separates the sides of a production, e.g. `A = a b c`
* in the Coco grammars "." terminates a production, but for readability
  in this document a production starts with the defined identifier in
  the left margin and may be continued on subsequent lines if they
  are indented
* `|` separates alternatives, e.g. `a b | c | d e` means `a b` or `c or d e`
* `(` `)` groups alternatives, e.g. `(a | b) c` means `a c` or `b c`
* `[ ]` option, e.g. `[a] b` means `a b` or `b`
* `{ }` iteration (0 or more times), e.g. `{a} b` means `b` or `a b` or `a a b` or ...
* We allow `|` inside `[ ]` and `{ }`. So `[a | b]` is short for `[(a | b)]`
  and `{a | b}` is short for `{(a | b)}`.
* The first production defines the name of the grammar, in this case `Dafny`.

In addition to the Coco rules, for the sake of readability we have adopted
these additional conventions.

* We allow `-` to be used. `a - b` means it matches if it matches `a` but not `b`.
* To aid in explaining the grammar we have added some additional productions
that are not present in the original grammar. We name these with a trailing
underscore. If you inline these where they are referenced, the result should
let you reconstruct the original grammar.

<!-- TODO: grammar hyperlinks are not implemented -->

## 2.1. Dafny Input {#sec-unicode}

Dafny source code files are readable text encoded as UTF-8 Unicode
(because this is what the Coco/R-generated scanner and parser read).
All program text other than the contents of comments, character, string and verbatim string literals
are printable and white-space ASCII characters,
that is, ASCII characters in the range `!` to `~`, plus space, tab, cr and nl (ASCII, 9, 10, 13, 32)  characters.

However, a current limitation of the Coco/R tool used by `dafny`
is that only printable and white-space ASCII characters can be used.
Use `\u` escapes in string and character literals to insert unicode characters.
Unicode in comments will work fine unless the unicode is interpreted as an end-of-comment indication.
Unicode in verbatim strings will likely not be interpreted as intended. [Outstanding issue #818].

## 2.2. Tokens and whitespace
The characters used in a Dafny program fall into four groups:

* White space characters
* alphanumerics: letters, digits, underscore (`_`), apostrophe (`'`), and question mark (`?`)
* punctuation: ``(){}[],.`;``
* operator characters (the other printable characters)

Each Dafny token consists of a sequence of consecutive characters from just one of these
groups, excluding white-space. White-space is ignored except that it
separates tokens.

A sequence of alphanumeric characters (with no preceding or following additional
alphanumeric characters) is a _single_ token. This is true even if the token
is syntactially or semantically invalid and the sequence could be separated into
more than one valid token. For example, `assert56` is one identifier token,
not a keyword `assert` followed by a number; `ifb!=0` begins with the token
`ifb` and not with the keyword `if` and token `b`; `0xFFFFZZ` is an illegal
token, not a valid hex number `0xFFFF` followed by an identifier `ZZ`.
White-space must be used to separate two such tokens in a program.

Somewhat differently, operator tokens need not be separated.
Only specific sequences of operator characters are recognized and these
are somewhat context-sensitive. For example, in `seq<set<int>>`, the grammar
knows that `>>` is two individual `>` tokens terminating the nested
type parameter lists; the right shift operator `>>` would never be valid here. Similarly, the
sequence `==>` is always one token; even if it were invalid in its context,
separating it into `==` and `>` would always still be invalid.

In summary, except for required white space between alphanumeric tokens,
adding white space between tokens or removing white space can never result in changing the meaning of a Dafny program.
For the rest of this document, we consider Dafny programs as sequences of tokens.

## 2.3. Character Classes {#sec-character-classes}
This section defines character classes used later in the token definitions.
In this section a backslash is used to start an escape sequence; so for example
`'\n'` denotes the single linefeed character. Also in this section, double quotes
enclose the set of characters constituting a character class; enclosing single
quotes are used when there is just one character in the class. `+` indicates
the union of two character classes; `-` is the set-difference between the
two classes. `ANY` designates all [unicode characters](#sec-unicode).

````grammar
letter = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
````
At present, a letter is an ASCII upper or lowercase letter. Other Unicode letters
are not supported.

````grammar
digit = "0123456789"
````
A digit is just one of the base-10 digits.

````grammar
posDigit = "123456789"
posDigitFrom2 = "23456789"
````
A ``posDigit`` is a digit, excluding 0. ``posDigitFrom2`` excludes both 0 and 1.

````grammar
hexdigit = "0123456789ABCDEFabcdef"
````
A ``hexdigit`` character is a digit or one of the letters from 'A' to 'F' in either case.

````grammar
special = "'_?"
````
The _special_ characters are the characters in addition to alphanumeric characters
that are allowed to appear in a Dafny identifier. These are

* `'` because mathematicians like to put primes on identifiers and some ML
  programmers like to start names of type parameters with a `'`,
* `_` because computer scientists expect to be able to have underscores in identifiers, and
* `?` because it is useful to have `?` at the end of names of predicates,
  e.g., "Cons?".

````grammar
cr        = '\r'
````
A carriage return character.

````grammar
lf        = '\n'
````
A line feed character.

````grammar
tab       = '\t'
````
A tab character.

````grammar
space     = ' '
````
A space character.

````grammar
nondigitIdChar = letter + special
````
The characters that can be used in an identifier minus the digits.

````grammar
idchar = nondigitIdChar + digit
````
The characters that can be used in an identifier.

````grammar
nonidchar = ANY - idchar
````
Any character except those that can be used in an identifier.
Here the scanner generator will interpret `ANY` as any unicode character.
However, `nonidchar` is used only to mark the end of the `!in` token;
in this context any character other than [whitespace or printable ASCII](#sec-unicode)
will trigger a subsequent scanning or parsing error.

````grammar
charChar = ANY - '\'' - '\\' - cr - lf
````
Characters that can appear in a character constant.
See the [discussion on unicode support](#sec-unicode).

````grammar
stringChar = ANY - '"' - '\\' - cr - lf
````
Characters that can appear in a string constant.
See the [discussion on unicode support](#sec-unicode).

````grammar
verbatimStringChar = ANY - '"'
````
Characters that can appear in a verbatim string.
See the [discussion on unicode support](#sec-unicode).

## 2.4. Comments
Comments are in two forms.

* They may go from `/*` to `*/` .
* They may go from `//` to the end of the line.

Comments may be nested,
but note that the nesting of multi-line comments is behavior that is different
from most programming languages. In Dafny,
```dafny
method m() {
  /* comment
     /* nested comment
     */
     rest of outer comment
  */
}
```
is permitted; this feature is convenient for commenting out blocks of
program statements that already have multi-line comments within them.
Other than looking for  end-of-comment delimiters,
the contents of a comment are not interpreted.
Comments may contain any unicode character, but see the [discussion on unicode support](#sec-unicode) for more information.

Note that the nesting is not fool-proof. In
```dafny
method m() {
  /* var i: int;
     // */ line comment
     var j: int;
  */
}
```
and
```dafny
method m() {
  /* var i: int;
     var s: string := "a*/b";
     var j: int;
   */
}
```
the `*/` inside the line comment and the string are seen as the end of the outer
comment, leaving trailing text that will provoke parsing errors.

## 2.5. Tokens {#sec-tokens}
As with most languages, Dafny syntax is defined in two levels. First the stream
of input characters is broken up into _tokens_. Then these tokens are parsed
using the Dafny grammar. The Dafny tokens are defined in this section.

### 2.5.1. Reserved Words
The following reserved words appear in the Dafny grammar and may not be used
as identifiers of user-defined entities:

````grammar
reservedword =
    "abstract" | "allocated" | "as" | "assert" | "assume" |
    "bool" | "break" | "by" |
    "calc" | "case" | "char" | "class" | "codatatype" |
    "colemma" | "const" | "constructor" | "copredicate" |
    "datatype" | "decreases" |
    "else" | "ensures" | "exists" | "export" | "extends" |
    "false" | "forall" | "fresh" | "function" | "ghost" |
    "if" | "imap" | "import" | "in" | "include" | "inductive" |
    "int" | "invariant" | "is" | "iset" | "iterator" |
    "label" | "lemma" | "map" | "match" | "method" |
    "modifies" | "modify" | "module" | "multiset" |
    "nameonly" | "nat" | "new" | "newtype" | "null" |
    "object" | "object?" | "old" | "opened" | "ORDINAL"
    "predicate" | "print" | "provides" |
    "reads" | "real" | "refines" | "requires" | "return" |
    "returns" | "reveal" | "reveals" |
    "seq" | "set" | "static" | "string" |
    "then" | "this" | "trait" | "true" | "twostate" | "type" |
    "unchanged" | "var" | "while" | "witness" |
    "yield" | "yields" |
    arrayToken | bvToken

arrayToken = "array" [ posDigitFrom2 | posDigit digit { digit }]["?"]

bvToken = "bv" ( 0 | posDigit { digit } )
````

An ``arrayToken`` is a reserved word that denotes an array type of
given rank. `array` is an array type of rank 1 (aka a vector). `array2`
is the type of two-dimensional arrays, etc.
`array1` and `array1?` are not reserved words; they are just ordinary identifiers.
Similarly, `bv0`, `bv1`, and `bv8` are reserved words, but `bv02` is an
ordinary identifier.

### 2.5.2. Identifiers

````grammar
ident = nondigitIdChar { idchar } - charToken - reservedword
````
In general Dafny identifiers are sequences of ``idchar`` characters where
the first character is a ``nondigitIdChar``. However tokens that fit this pattern
are not identifiers if they look like a character literal
or a reserved word (including array or bit-vector type tokens).
Also, `ident` tokens that begin with an `_` are not permitted as user identifiers.

### 2.5.3. Digits
````grammar
digits = digit {['_'] digit}
````

A sequence of decimal digits, possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
Example: `1_234_567`.
````grammar
hexdigits = "0x" hexdigit {['_'] hexdigit}
````

A hexadecimal constant, possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
Example: `0xffff_ffff`.

````grammar
decimaldigits = digit {['_'] digit} '.' digit {['_'] digit}
````
A decimal fraction constant, possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
Example: `123_456.789_123`.

### 2.5.4. Escaped Character
In this section the "\\" characters are literal.
````grammar
escapedChar =
    ( "\'" | "\"" | "\\" | "\0" | "\n" | "\r" | "\t"
      | "\u" hexdigit hexdigit hexdigit hexdigit
    )
````

In Dafny character or string literals, escaped characters may be used
to specify the presence of a single- or double-quote character, backslash,
null, new line, carriage return, tab, or a
Unicode character with given hexadecimal representation.

### 2.5.5. Character Constant Token
````grammar
charToken = "'" ( charChar | escapedChar ) "'"
````

A character constant is enclosed by `'` and includes either a character
from the ``charChar`` set or an escaped character. Note that although Unicode
letters are not allowed in Dafny identifiers, Dafny does support [Unicode
in its character, string, and verbatim strings constants and in its comments](#sec-unicode). A character
constant has type `char`.


### 2.5.6. String Constant Token
````grammar
stringToken =
    '"' { stringChar | escapedChar }  '"'
  | '@' '"' { verbatimStringChar | '"' '"' } '"'
````

A string constant is either a normal string constant or a verbatim string constant.
A normal string constant is enclosed by `"` and can contain characters from the
``stringChar`` set and escapes.

A verbatim string constant is enclosed between `@"` and `"` and can
consist of any characters (including newline characters) except that two
successive double quotes represent one quote character inside
the string. This is the mechanism for escaping a double quote character,
which is the only character needing escaping in a verbatim string.

### 2.5.7. Ellipsis
````grammar
ellipsis = "..."
````
The ellipsis symbol is typically used to designate something missing that will
later be inserted through refinement or is already present in a parent declaration..

## 2.6. Low Level Grammar Productions {#sec-grammar}

### 2.6.1. Identifier Variations

````grammar
Ident = ident
````
The ``Ident`` non-terminal is just an ``ident`` token and represents an ordinary
identifier.

````grammar
DotSuffix =
  ( ident | digits | "requires" | "reads" )
````
When using the _dot_ notation to denote a component of a compound entity,
the token following the "." may be an identifier,
 a natural number, or one of the keywords `requires` or `reads`.

* Digits can be used to name fields of classes and destructors of
  datatypes. For example, the built-in tuple datatypes have destructors
  named 0, 1, 2, etc. Note that as a field or destructor name a digit sequence
  is treated as a string, not a number: internal
  underscores matter, so `10` is different from `1_0` and from `010`.
* `m.requires` is used to denote the precondition for method `m`.
* `m.reads` is used to denote the things that method `m` may read.

````grammar
NoUSIdent = ident - "_" { idchar }
````
A ``NoUSIdent`` is an identifier except that identifiers with a **leading**
underscore are not allowed. The names of user-defined entities are
required to be ``NoUSIdent``s or, in some contexts, a ``digits``.
 We introduce more mnemonic names
for these below (e.g. ``ClassName``).

````grammar
WildIdent = NoUSIdent | "_"
````
Identifier, disallowing leading underscores, except the "wildcard"
identifier `_`. When `_` appears it is replaced by a unique generated
identifier distinct from user identifiers. This wildcard has several uses
in the language, but it is not used as part of expressions.

### 2.6.2. NoUSIdent Synonyms
In the productions for the declaration of user-defined entities the name of the
user-defined entity is required to be an identifier that does not start
with an underscore, i.e., a ``NoUSIdent``. To make the productions more
mnemonic, we introduce the following synonyms for ``NoUSIdent``
and other identifier-related symbols.

````grammar
IdentOrDigits = Ident | digits
NoUSIdentOrDigits = NoUSIdent | digits
ModuleName = NoUSIdent
ClassName = NoUSIdent    // also traits
DatatypeName = NoUSIdent
DatatypeMemberName = NoUSIdentOrDigits
NewtypeName = NoUSIdent
SynonymTypeName = NoUSIdent
IteratorName = NoUSIdent
TypeVariableName = NoUSIdent
MethodFunctionName = NoUSIdentOrDigits
LabelName = NoUSIdentOrDigits
AttributeName = NoUSIdent
ExportId = NoUSIdentOrDigits
TypeNameOrCtorSuffix = NoUSIdentOrDigits
````

Some parsing constexts

### 2.6.3. Qualified Names
```grammar
QualifiedModuleName = ModuleName { "." ModuleName }
```
A qualified name starts with the name of the top-level entity and then is followed by
zero or more ``DotSuffix``s which denote a component. Examples:

* `Module.MyType1`
* `MyTuple.1`
* `MyMethod.requires`
* `A.B.C.D`

The grammar does not actually have a production for qualified names
except in the special case of a qualified name that is known to be
a module name, i.e. a ``QualifiedModuleName``.

### 2.6.4. Identifier-Type Combinations
In this section, we describe some nonterminals that combine an identifier and a type.

````grammar
IdentType = WildIdent ":" Type
````
In Dafny, a variable or field is typically declared by giving its name followed by
a ``colon`` and its type. An ``IdentType`` is such a construct.

````grammar
FIdentType = NoUSIdentOrDigits ":" Type
````
A `FIdentType` is used to declare a field. The Type is required because there is no initializer.

````grammar
CIdentType = NoUSIdentOrDigits [ ":" Type ]
````
A `CIdentType` is used for a `const` declaration. The Type is optional because it may be inferred from
the initializer.

````grammar
GIdentType(allowGhostKeyword, allowNewKeyword, allowNameOnlyKeyword, allowDefault) =
    { "ghost" | "new" | "nameonly" } IdentType
    [ ":=" Expression(allowLemma: true, allowLambda: true) ]
````
A ``GIdentType`` is a typed entity declaration optionally preceded by `ghost` or `new`. The _ghost_
qualifier means the entity is only used during verification and not in the generated code.
Ghost variables are useful for abstractly representing internal state in specifications.
If `allowGhostKeyword` is false, then `ghost` is not allowed.
If `allowNewKeyword` is false, then `new` is not allowed.
If `allowNameOnlyKeyword` is false, then `nameonly` is not allowed.
If `allowDefault` is false, then `:= Expression` is not allowed.

````grammar
LocalIdentTypeOptional = WildIdent [ ":" Type ]
````
A ``LocalIdentTypeOptional`` is used when declaring local variables.
If a value is specified for the variable, the
type may be omitted because it can be inferred from the initial value.
An initial value is not required.

````grammar
IdentTypeOptional = WildIdent [ ":" Type ]
````
A ``IdentTypeOptional`` is typically used in a context where the type of the identifier
may be inferred from the context. Examples are in pattern matching or quantifiers.

````grammar
TypeIdentOptional =
    { "ghost" | "nameonly" } [ NoUSIdentOrDigits ":" ] Type
    [ ":=" Expression(allowLemma: true, allowLambda: true) ]
````
``TypeIdentOptional``s are used in ``FormalsOptionalIds``. This represents situations
where a type is given but there may not be an identifier. The default-value expression
`:= Expression` is allowed only if `NoUSIdentOrDigits :` is also provided.
If modifier `nameonly` is given, then `NoUSIdentOrDigits` must also be used.

````grammar
FormalsOptionalIds = "(" [ TypeIdentOptional
                           { "," TypeIdentOptional } ] ")"
````
A ``FormalsOptionalIds`` is a formal parameter list in which the types are required
but the names of the parameters are optional. This is used in algebraic
datatype definitions.

### 2.6.5. Numeric Literals
````grammar
Nat = ( digits | hexdigits )
````
A ``Nat`` represents a natural number expressed in either decimal or hexadecimal.

````grammar
Dec = decimaldigits
````
A ``Dec`` represents a decimal fraction literal.

