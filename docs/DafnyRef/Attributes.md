# 23. Attributes {#sec-attributes}
Dafny allows many of its entities to be annotated with _Attributes_.
Attributes are declared between `{:` and `}` like this:
```dafny
{:attributeName "argument", "second" + "argument", 57}
```
(White-space may follow but not precede the `:` in `{:`.)

In general an attribute may have any name the user chooses. It may be
followed by a comma-separated list of expressions. These expressions will
be resolved and type-checked in the context where the attribute appears.

Any Dafny entity may have a list of attributes.
Dafny does not check that the attributes listed for an entity
are appropriate for it (which means that misspellings may
go silently unnoticed).

The grammar shows where the attribute annotations may appear:
````grammar
Attribute = "{:" AttributeName [ Expressions ] "}"
````

Dafny has special processing for some attributes[^boogie-attributes].  Of those,
some apply only to the entity bearing the attribute, while others (inherited
attributes) apply to the entity and its descendants (such as nested modules,
types, or declarations).  The attribute declaration closest to the entity
overrides those further away.

[^boogie-attributes]: All entities that Dafny translates to Boogie have their attributes passed on to Boogie except for the [`{:axiom}`](#sec-axiom) attribute (which conflicts with Boogie usage) and the [`{:trigger}`](#sec-trigger) attribute which is instead converted into a Boogie quantifier _trigger_. See Section 11 of [@Leino:Boogie2-RefMan].

For attributes with a single boolean expression argument, the attribute
with no argument is interpreted as if it were true.

## 23.1. Attributes on top-level declarations

### 23.1.1. `{:autocontracts}` {#sec-attributes-autocontracts}
Dynamic frames [@Kassios:FM2006;@SmansEtAl:VeriCool;@SmansEtAl:ImplicitDynamicFrames;
@LEINO:Dafny:DynamicFrames]
are frame expressions that can vary dynamically during
program execution. AutoContracts is an experimental feature that will
fill much of the dynamic-frames boilerplate into a class.

From the user's perspective, what needs to be done is simply:

* mark the class with `{:autocontracts}`
* declare a function (or predicate) called `Valid()`


AutoContracts will then:

*  Declare:
```dafny
   ghost var Repr: set<object>
```

* For function/predicate `Valid()`, insert:
```dafny
   reads this, Repr
```
* Into body of `Valid()`, insert (at the beginning of the body):
```dafny
   this in Repr && null !in Repr
```
* and also insert, for every array-valued field `A` declared in the class:
```dafny
   && (A != null ==> A in Repr)
```
* and for every field `F` of a class type `T` where `T` has a field called `Repr`, also insert:
```dafny
   (F != null ==> F in Repr && F.Repr <= Repr && this !in F.Repr)
```
  Except, if A or F is declared with `{:autocontracts false}`, then the implication will not
be added.

* For every constructor, add:
```dafny
   modifies this
   ensures Valid() && fresh(Repr - {this})
```
* At the end of the body of the constructor, add:
```dafny
   Repr := {this};
   if (A != null) { Repr := Repr + {A}; }
   if (F != null) { Repr := Repr + {F} + F.Repr; }
```
* For every method, add:
```dafny
   requires Valid()
   modifies Repr
   ensures Valid() && fresh(Repr - old(Repr))
```
* At the end of the body of the method, add:
```dafny
   if (A != null) { Repr := Repr + {A}; }
   if (F != null) { Repr := Repr + {F} + F.Repr; }
```

### 23.1.2. `{:nativeType}` {#sec-nativetype}
The `{:nativeType}` attribute may only be used on a ``NewtypeDecl``
where the base type is an integral type or a real type. For example:

```dafny
newtype {:nativeType "byte"} ubyte = x : int | 0 <= x < 256
newtype {:nativeType "byte"} ubyte = x : int | 0 <= x < 257 // Fails
```

It can take one of the following forms:

* `{:nativeType}` - With no parameters it has no effect and the ``NewtypeDecl``
will have its default behavior which is to choose a native type that can hold any
value satisfying the constraints, if possible, otherwise BigInteger is used.
* `{:nativeType true}` - Also gives default ``NewtypeDecl`` behavior,
but gives an error if the base type is not integral.
* `{:nativeType false}` - Inhibits using a native type. BigInteger is used.
* `{:nativeType "typename"}` - This form has an native integral
type name as a string literal. Acceptable values are:
   * `"byte"`      8 bits, unsigned
   * `"sbyte"`     8 bits, signed
   * `"ushort"`    16 bits, unsigned
   * `"short"`     16 bits, signed
   * `"uint"`      32 bits, unsigned
   * `"int"`       32 bits, signed
   * `"number"`    53 bits, signed
   * `"ulong"`     64 bits, unsigned
   * `"long"`      64 bits, signed

  If the target compiler
  does not support a named native type X, then an error is generated. Also, if, after
  scrutinizing the constraint predicate, the compiler cannot confirm
  that the type's values will fit in X, an error is generated.
  The names given above do not have to match the names in the target compilation language,
  just the characteristics of that type.

### 23.1.3. `{:ignore}` (deprecated)
Ignore the declaration (after checking for duplicate names).

### 23.1.4. `{:extern}` {#sec-extern}

`{:extern}` is a target-language dependent modifier used

* to alter the `CompileName` of entities such as modules, classes, methods, etc.,
* to alter the `ReferenceName` of the entities,
* to decide how to define external opaque types,
* to decide whether to emit target code or not, and
* to decide whether a declaration is allowed not to have a body.

The `CompileName` is the name for the entity when translating to one of the target languages.
The `ReferenceName` is the name used to refer to the entity in the target language.
A common use case of `{:extern}` is to avoid name clashes with existing library functions.

`{:extern}` takes 0, 1, or 2 (possibly empty) string arguments:

- `{:extern}`: Dafny will use the Dafny-determined name as the `CompileName` and not affect the `ReferenceName`
- `{:extern s1}`: Dafny will use `s1` as the `CompileName`, and replaces the last portion of the `ReferenceName` by `s1`.
     When used on an opaque type, s1 is used as a hint as to how to declare that type when compiling.
- `{:extern s1, s2}` Dafny will use `s2` as the `CompileName`.
     Dafny will use a combination of `s1` and `s2` such as for example `s1.s2` as the `ReferenceName`
     It may also be the case that one of the arguments is simply ignored.

Dafny does not perform sanity checks on the arguments---it is the user's responsibility not to generate
  malformed target code.

For more detail on the use of `{:extern}`, see the corresponding [section](#sec-extern-decls) in the user's guide.

## 23.2. Attributes on functions and methods

### 23.2.1. `{:autoReq}`
For a function declaration, if this attribute is set true at the nearest
level, then its `requires` clause is strengthened sufficiently so that
it may call the functions that it calls.

For following example
```dafny
function f(x:int) : bool
  requires x > 3
{
  x > 7
}

// Should succeed thanks to auto_reqs
function {:autoReq} g(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}
```
the `{:autoReq}` attribute causes Dafny to
deduce a `requires` clause for g as if it had been
declared
```dafny
function g(y:int, b:bool) : bool
  requires if b then y + 2 > 3 else 2 * y > 3
{
  if b then f(y + 2) else f(2*y)
}
```

### 23.2.2. `{:axiom}` {#sec-axiom}
The `{:axiom}` attribute may be placed on a function or method.
It means that the post-condition may be assumed to be true
without proof. In that case also the body of the function or
method may be omitted.

The `{:axiom}` attribute only prevents Dafny from verifying that the body matches the post-condition.
Dafny still verifies the well-formedness of pre-conditions, of post-conditions, and of the body if provided.
To prevent Dafny from running all these checks, one would use [`{:verify false}`](#sec-verify), which is not recommended.

The compiler will still emit code for an [`{:axiom}`](#sec-axiom), if it is a [`function method`, a `method` or a `function by method`](#sec-function-declarations) with a body.

### 23.2.3. `{:compile}`
The `{:compile}` attribute takes a boolean argument. It may be applied to
any top-level declaration. If that argument is false, then that declaration
will not be compiled at all.
The difference with [`{:extern}`](#sec-extern) is that [`{:extern}`](#sec-extern)
will still emit declaration code if necessary,
whereas `{:compile false}` will just ignore the declaration for compilation purposes.

### 23.2.4. `{:extern <name>}` {#sec-extern-method}
See [`{:extern <name>}`](#sec-extern).

### 23.2.5. `{:fuel X}` {#sec-fuel}
The fuel attributes is used to specify how much "fuel" a function should have,
i.e., how many times the verifier is permitted to unfold its definition.  The
`{:fuel}` annotation can be added to the function itself, it which
case it will apply to all uses of that function, or it can be overridden
within the scope of a module, function, method, iterator, calc, forall,
while, assert, or assume.  The general format is:

```dafny
{:fuel functionName,lowFuel,highFuel}
```

When applied as an annotation to the function itself, omit
functionName.  If highFuel is omitted, it defaults to lowFuel + 1.

The default fuel setting for recursive functions is 1,2.  Setting the
fuel higher, say, to 3,4, will give more unfoldings, which may make
some proofs go through with less programmer assistance (e.g., with
fewer assert statements), but it may also increase verification time,
so use it with care.  Setting the fuel to 0,0 is similar to making the
definition opaque, except when used with all literal arguments.

### 23.2.6. `{:id <string>}`
Assign a custom unique ID to a function or a method to be used for verification
result caching.

### 23.2.7. `{:induction}` {#sec-induction}
The `{:induction}` attribute controls the application of
proof by induction to two contexts. Given a list of
variables on which induction might be applied, the
`{:induction}` attribute selects a sub-list of those
variables (in the same order) to which to apply induction.

Dafny issue [34](https://github.com/Microsoft/dafny/issues/34)
proposes to remove the restriction that the sub-list
be in the same order, and would apply induction in the
order given in the `{:induction}` attribute.

The two contexts are:

* A method, in which case the bound variables are all the
  in-parameters of the method.
* A [quantifier expression](#sec-induction-quantifier), in which case the bound variables
  are the bound variables of the quantifier expression.

The form of the `{:induction}` attribute is one of the following:

* `{:induction}` -- apply induction to all bound variables
* `{:induction false}` -- suppress induction, that is, don't apply it to any bound variable
* `{:induction L}` where `L` is a list consisting entirely of bound variables
-- apply induction to the specified bound variables
* `{:induction X}` where `X` is anything else -- treat the same as
`{:induction}`, that is, apply induction to all bound variables. For this
usage conventionally `X` is `true`.

Here is an example of using it on a quantifier expression:
```dafny
lemma Fill_J(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
  ensures forall i,j {:induction j} :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}
```

### 23.2.8. `{:opaque}` {#sec-opaque}
Ordinarily, the body of a function is transparent to its users, but
sometimes it is useful to hide it. If a function `foo` or `bar` is given the
`{:opaque}` attribute, then Dafny hides the body of the function,
so that it can only be seen within its recursive clique (if any),
or if the programmer specifically asks to see it via the statement `reveal foo(), bar();`.

More information about the Boogie implementation of `{:opaque}` is [here](https://github.com/dafny-lang/dafny/blob/master/docs/Compilation/Boogie.md).

### 23.2.9. `{:print}` {#sec-print}
This attribute declares that a method may have print effects,
that is, it may use `print` statements and may call other methods
that have print effects. The attribute can be applied to compiled
methods, constructors, and iterators, and it gives an error if
applied to functions or ghost methods. An overriding method is
allowed to use a `{:print}` attribute only if the overridden method
does.
Print effects are enforced only with `/trackPrintEffects:1`.

<!--
Describe this where refinement is described, as appropriate.

-### 22.1.15. prependAssertToken
This is used internally in Dafny as part of module refinement.
It is an attribute on an assert statement.
The Dafny code has the following comment:

```dafny
// Clone the expression, but among the new assert's attributes, indicate
// that this assertion is supposed to be translated into a check.  That is,
// it is not allowed to be just assumed in the translation, despite the fact
// that the condition is inherited.
```

TODO: Decide if we want to describe this in more detail, or whether
the functionality is already adequately described where
refinement is described.
-->

### 23.2.10. `{:priority}`
`{:priority N}` assigns a positive priority 'N' to a method or function to control the order
in which methods or functions are verified (default: N = 1).

### 23.2.11. `{:rlimit}` {#sec-rlimit}

`{:rlimit N}` limits the verifier resource usage to verify the method or function at `N * 1000`.
This is the per-method equivalent of the command-line flag `/rlimit:N`.
If using [`{:vcs_split_on_every_assert}`](#sec-vcs_split_on_every_assert) as well, the limit will be set for each assertion.

To give orders of magnitude about resource usage, here is a list of examples indicating how many resources are used to verify each method:

* 8K resource usage
  ```dafny
  method f() {
    assert true;
  }
  ```
* 10K resource usage using assertions that do not add assumptions:
  ```dafny
  method f() {
    assert a: (a ==> b) <==> (!b ==> !a);
    assert b: (a ==> b) <==> (!b ==> !a);
    assert c: (a ==> b) <==> (!b ==> !a);
    assert d: (a ==> b) <==> (!b ==> !a);
  }
  ```

* 40K total resource usage using [`{:vcs_split_on_every_assert}`](#sec-vcs_split_on_every_assert)
  ```dafny
  method {:vcs_split_on_every_assert} f(a: bool, b: bool) {
    assert a: (a ==> b) <==> (!b ==> !a);
    assert b: (a ==> b) <==> (!b ==> !a);
    assert c: (a ==> b) <==> (!b ==> !a);
    assert d: (a ==> b) <==> (!b ==> !a);
  }
  ```
*  37K total resource usage and thus fails with `out of resource`.
   ```dafny
   method {:rlimit 30} f(a: int, b: int, c: int) {
     assert ((1 + a*a)*c) / (1 + a*a) == c;
   }
   ```

Note that, the default solver Z3 tends to overshoot by `7K` to `8K`, so if you put `{:rlimit 20}` in the last example, the total resource usage would be `27K`.

### 23.2.12. `{:selective_checking}`
Turn all assertions into assumptions except for the ones reachable from after the
assertions marked with the attribute `{:start_checking_here}`.
Thus, `assume {:start_checking_here} something;` becomes an inverse
of `assume false;`: the first one disables all verification before
it, and the second one disables all verification after.

### 23.2.13. `{:tailrecursion}`
This attribute is used on method declarations. It has a boolean argument.

If specified with a `false` value, it means the user specifically
requested no tail recursion, so none is done.

If specified with a `true` value, or if no argument is specified,
then tail recursive optimization will be attempted subject to
the following conditions:

* It is an error if the method is a ghost method and tail
recursion was explicitly requested.
* Only direct recursion is supported, not mutually recursive methods.
* If `{:tailrecursion true}` was specified but the code does not allow it,
an error message is given.

### 23.2.14. `{:test}` {#sec-test-attribute}
This attribute indicates the target function or method is meant
to be executed at runtime in order to test that the program is working as intended.

There are two different ways to dynamically test functionality in a test:

1. A test can optionally return a single value to indicate success or failure.
   If it does, this must be a _failure-compatible_ type
   just as the [update-with-failure statement](#sec-update-failure) requires. That is,
   the returned type must define a `IsFailure()` function method. If `IsFailure()`
   evaluates to `true` on the return value, the test will be marked a failure, and this
   return value used as the failure message.
2. Code in the control flow of the test can use [`expect` statements](#sec-expect-statement)
   to dynamically test if a boolean expression is true, and cause the test to halt
   if not (but not the overall testing process). The optional second argument to 
   a failed `expect` statement will be used as the test failure message.

Note that the `expect` keyword can also be used to form "assign or halt" statements
such as `var x :- expect CalculateX();`, which is a convenient way to invoke a method
that may produce a failure within a test without having to return a value from the test.

There are also two different approaches to executing all tests in a program:

1. By default, the compiler will mark each compiled method as necessary so that
   a designated target language testing framework will discover and run it.
   This is currently only implemented for C#, using the xUnit `[Fact]` annotation.
2. If the `/runAllTests:1` option is provided, Dafny will instead produce a main method
   that invokes each test and prints the results.
   This runner is currently very basic, but avoids introducing any additional target
   language dependencies in the compiled code.

### 23.2.15. `{:timeLimit N}` {#sec-time-limit}
Set the time limit for verifying a given function or method.

### 23.2.16. `{:timeLimitMultiplier X}`
This attribute may be placed on a method or function declaration
and has an integer argument. If `{:timeLimitMultiplier X}` was
specified a `{:timeLimit Y}` attribute is passed on to Boogie
where `Y` is `X` times either the default verification time limit
for a function or method, or times the value specified by the
Boogie `-timeLimit` command-line option.

### 23.2.17. `{:verify false}` {#sec-verify}
     
Skip verification of a function or a method altogether,
not even trying to verify the well-formedness of postconditions and preconditions.
We discourage using this attribute and prefer [`{:axiom}`](#sec-axiom),
which performs these minimal checks while not checking that the body satisfies the postconditions.

### 23.2.18. `{:vcs_max_cost N}` {#sec-vcs_max_cost}
Per-method version of the command-line option `/vcsMaxCost`.

The [assertion batch](#sec-assertion-batches) of a method
will not be split unless the cost of an [assertion batch](#sec-assertion-batches) exceeds this
number, defaults to 2000.0. In
[keep-going mode](#sec-vcs_max_keep_going_splits), only applies to the first round.
If [`{:vcs_split_on_every_assert}`](#sec-vcs_split_on_every_assert) is set, then this parameter is useless.

### 23.2.19. `{:vcs_max_keep_going_splits N}` {#sec-vcs_max_keep_going_splits}

Per-method version of the command-line option `/vcsMaxKeepGoingSplits`.
If set to more than 1, activates the _keep going mode_ where, after the first round of splitting,
[assertion batches](#sec-assertion-batches) that timed out are split into N [assertion batches](#sec-assertion-batches) and retried
until we succeed proving them, or there is only one
single assertion that it timeouts (in which
case an error is reported for that assertion).
Defaults to 1.
If [`{:vcs_split_on_every_assert}`](#sec-vcs_split_on_every_assert) is set, then this parameter is useless.

### 23.2.20. `{:vcs_max_splits N}` {#sec-vcs_max_splits}

Per-method version of the command-line option `/vcsMaxSplits`.
Maximal number of [assertion batches](#sec-assertion-batches) generated for this method.
In [keep-going mode](#sec-vcs_max_keep_going_splits), only applies to the first round.
Defaults to 1.
If [`{:vcs_split_on_every_assert}`](#sec-vcs_split_on_every_assert) is set, then this parameter is useless.

### 23.2.21. `{:vcs_split_on_every_assert}` {#sec-vcs_split_on_every_assert}
Per-method version of the command-line option `/vcsSplitOnEveryAssert`.

In the first and only verification round, this option will split the original [assertion batch](#sec-assertion-batches)
into one assertion batch per assertion.
This is mostly helpful for debugging which assertion is taking the most time to prove, e.g. to profile them.

### 23.2.22. `{:synthesize}` {#sec-synthesize-attr}

The `{:synthesize}` attribute must be used on methods that have no body and
return one or more fresh objects. During compilation, 
the postconditions associated with such a
method are translated to a series of API calls to the target languages's
mocking framework. The object returned, therefore, behaves exactly as the
postconditions specify. If there is a possibility that this behavior violates
the specifications on the object's instance methods or hardcodes the values of
its fields, the compiler will throw an error but the compilation will go
through. Currently, this compilation pass is only supported in C# and requires
adding the latest version of the Moq library to the .csproj file before
generating the binary.

Not all Dafny postconditions can be successfully compiled - below is the
grammar for postconditions that are supported (`S` is the start symbol, `EXPR`
stands for an arbitrary Dafny expression, and `ID` stands for
variable/method/type identifiers):

```
S         = FORALL
          | EQUALS
          | S && S
EQUALS    = ID.ID (ARGLIST) == EXPR // stubs a function call
          | ID.ID           == EXPR // stubs field access
          | EQUALS && EQUALS
FORALL    = forall BOUNDVARS :: EXPR ==> EQUALS
ARGLIST   = ID   // this can be one of the bound variables
          | EXPR // this expr may not reference any of the bound variables
          | ARGLIST, ARGLIST
BOUNDVARS = ID : ID
          | BOUNDVARS, BOUNDVARS
```

### 23.2.23. `{:options OPT0, OPT1, ... }` {#sec-attr-options}

This attribute applies only to modules. It configures Dafny as if
`OPT0`, `OPT1`, … had been passed on the command line.  Outside of the module,
options revert to their previous values.

Only a small subset of Dafny's command line options is supported.  Use the
`/attrHelp` flag to see which ones.

## 23.3. Attributes on assertions, preconditions and postconditions {#sec-verification-attributes-on-assert-statements}


### 23.3.1. `{:focus}` {#sec-focus}
`assert {:focus} X;` splits verification into two [assertion batches](#sec-assertion-batches).
The first batch considers all assertions that are not on the block containing the `assert {:focus} X;`
The second batch considers all assertions that are on the block containing the `assert {:focus} X;` and those that will _always_ follow afterwards.
Hence, it might also occasionally double-report errors.
If you truly want a split on the batches, prefer [`{:split_here}`](#sec-split_here).

Here are two examples illustrating how `{:focus}` works, where `--` in the comments stands for `Assumption`:
```dafny
method doFocus1(x: bool) returns (y: int) {
  y := 1;                     // Batch 1    Batch 2
  assert y == 1;              // Assertion  --
  if x {
    if false {
      assert y >= 0;          // --         Assertion
      assert {:focus} y <= 2; // --         Assertion
      y := 2;
      assert y == 2;          // --         Assertion
    }
  } else {
    assert y == 1;            // Assertion  --
  }
  assert y == 1;              // Assertion  Assertion
  if !x {
    assert y >= 1;            // Assertion  Assertion
  } else {
    assert y <= 1;            // Assertion  Assertion
  }
}
```

And another one where the focused block is guarded with a `while`, resulting in remaining assertions not being part of the first assertion batch:
```dafny
method doFocus2(x: bool) returns (y: int) {
  y := 1;                     // Batch 1    Batch 2
  assert y == 1;              // Assertion  --
  if x {
    while false {
      assert y >= 0;          // --         Assertion
      assert {:focus} y <= 2; // --         Assertion
      y := 2;
      assert y == 2;          // --         Assertion
    }
  } else {
    assert y == 1;            // Assertion  --
  }
  assert y == 1;              // Assertion  --
  if !x {
    assert y >= 1;            // Assertion  --
  } else {
    assert y <= 1;            // Assertion  --
  }
}
```

### 23.3.2. `{:split_here}` {#sec-split_here}
`assert {:split_here} X;` splits verification into two [assertion batches](#sec-assertion-batches).
It verifies the code leading to this point (excluded) in a first assertion batch,
and the code leading from this point (included) to the next `{:split_here}` or until the end in a second assertion batch.
It might help with timeouts.

Here is one example, where `--` in the comments stands for `Assumption`:
```dafny
method doSplitHere(x: bool) returns (y: int) {
  y := 1;                      // Batch 1    Batch 2     Batch 3
  assert y >= 0;               // Assertion  --          --
  if x {
    assert y <= 1;             // Assertion  --          --
    assert {:split_here} true; // --         Assertion   --
    assert y <= 2;             // --         Assertion   --
    assert {:split_here} true; // --         --          Assertion
    if x {
      assert y == 1;           // --         --          Assertion
    } else {
      assert y >= 1;           // --         --          Assertion
    }
  } else {
    assert y <= 3;             // Assertion  --          --
  }
  assert y >= -1;              // Assertion  --          --
}
```

### 23.3.3. `{:subsumption n}`
Overrides the `/subsumption` command-line setting for this assertion.

## 23.4. Attributes on variable declarations

### 23.4.1. `{:assumption}`
This attribute can only be placed on a local ghost bool
variable of a method. Its declaration cannot have a rhs, but it is
allowed to participate as the lhs of exactly one assignment of the
form: `b := b && expr;`. Such a variable declaration translates in the
Boogie output to a declaration followed by an `assume b` command.
See [@LeinoWuestholz2015], Section 3, for example uses of the `{:assumption}`
attribute in Boogie.

## 23.5. Attributes on quantifier expressions (forall, exists)

### 23.5.1. `{:heapQuantifier}`
The `{:heapQuantifier}` attribute may be used on a [`QuantifierExpression`](#sec-quantifier-expression).
When it appears in a quantifier expression, it is as if a new heap-valued
quantifier variable was added to the quantification. Consider this code
that is one of the invariants of a while loop.

```dafny
invariant forall u {:heapQuantifier} :: f(u) == u + r
```

The quantifier is translated into the following Boogie:

```
(forall q$heap#8: Heap, u#5: int ::
    {:heapQuantifier}
    $IsGoodHeap(q$heap#8) && ($Heap == q$heap#8 || $HeapSucc($Heap, q$heap#8))
       ==> $Unbox(Apply1(TInt, TInt, f#0, q$heap#8, $Box(u#5))): int == u#5 + r#0);
```

What this is saying is that the quantified expression, `f(u) == u + r`,
which may depend on the heap, is also valid for any good heap that is either the
same as the current heap, or that is derived from it by heap update operations.

### 23.5.2. `{:induction}` {#sec-induction-quantifier}
See [`{:induction}`](#sec-induction) for functions and methods.

### 23.5.3. `{:layerQuantifier}`
The word 'layer' actually refers to the [`{:fuel}`](#sec-fuel).
When Dafny is translating a quantified expression, if it has
a `{:layerQuantifier}` attribute an additional quantifier
variable is added to the quantifier bound variables.
This variable has the predefined _LayerType_.
A `{:layerQuantifier}` attribute may be placed on a quantifier expression.
Translation of Dafny into Boogie defines a _LayerType_ which has defined zero and
successor constructors.

The Dafny source has the comment that "if a function is recursive,
then make the reveal lemma quantifier a layerQuantifier."
And in that case it adds the attribute to the quantifier.

There is no explicit use of the `{:layerQuantifier}` attribute
in the Dafny tests. So I believe this attribute is only used
internally by Dafny and not externally.

TODO: Need more complete explanation of this attribute.
Dafny issue [35](https://github.com/Microsoft/dafny/issues/35) tracks
further effort for this attribute.

### 23.5.4. `{:trigger}` {#sec-trigger}
Trigger attributes are used on quantifiers and comprehensions.

The verifier instantiates the body of a quantified expression only when it can find an expression that matches the provided trigger.  

Here is an example:
```dafny
predicate P(i: int)
predicate Q(i: int)

lemma PHoldEvenly()
  ensures  forall i {:trigger Q(i)} :: P(i) ==> P(i + 2) && Q(i)

lemma PHoldsForTwo()
  ensures forall i :: P(i) ==> P(i + 4)
{
  forall j: int
    ensures P(j) ==> P(j + 4)
  {
    if P(j) {
      assert P(j); // Trivial assertion
      
      PHoldEvenly();
      // Invoking the lemma assumes `forall i :: P(i) ==> P(i + 4)`,
      // but it's not instantiated yet
      
      // The verifier sees `Q(j)`, so it instantiates
      // `forall i :: P(i) ==> P(i + 4)` with `j`
      // and we get the axiom `P(j) ==> P(j + 2) && Q(j)`
      assert Q(j);     // hence it can prove `Q(j)`
      assert P(j + 2); //   and it can prove `P(j + 2)`
      assert P(j + 4); // But it cannot prove this
      // because it did not instantiate `forall i :: P(i) ==> P(i + 4)` with `j+2`
    }
  }
}
```

Here are ways one can prove `assert P(j + 4);`:
* Add `assert Q(j + 2);` just before `assert P(j + 4);`, so that the verifier sees the trigger.
* Change the trigger `{:trigger Q(i)}` to `{:trigger P(i)}` (replace the trigger)
* Change the trigger `{:trigger Q(i)}` to `{:trigger Q(i)} {:trigger P(i)}` (add a trigger)
* Remove `{:trigger Q(i)}` so that it will automatically determine all possible triggers thanks to the option `/autoTriggers:1` which is the default.



## 23.6. Other undocumented verification attributes

A scan of Dafny's sources shows it checks for the
following attributes.

* `{:$}`
* `{:$renamed$}`
* `{:InlineAssume}`
* `{:PossiblyUnreachable}`
* `{:__dominator_enabled}`
* `{:__enabled}`
* `{:a##post##}`
* `{:absdomain}`
* `{:ah}`
* `{:assumption}`
* `{:assumption_variable_initialization}`
* `{:atomic}`
* `{:aux}`
* `{:both}`
* `{:bvbuiltin}`
* `{:candidate}`
* `{:captureState}`
* `{:checksum}`
* `{:constructor}`
* `{:datatype}`
* `{:do_not_predicate}`
* `{:entrypoint}`
* `{:existential}`
* `{:exitAssert}`
* `{:expand}`
* `{:extern}`
* `{:focus}`
* `{:hidden}`
* `{:ignore}`
* `{:inline}`
* `{:left}`
* `{:linear}`
* `{:linear_in}`
* `{:linear_out}`
* `{:msg}`
* `{:name}`
* `{:originated_from_invariant}`
* `{:partition}`
* `{:positive}`
* `{:post}`
* `{:pre}`
* `{:precondition_previous_snapshot}`
* `{:qid}`
* `{:right}`
* `{:selective_checking}`
* `{:si_fcall}`
* `{:si_unique_call}`
* `{:sourcefile}`
* `{:sourceline}`
* `{:split_here}`
* `{:stage_active}`
* `{:stage_complete}`
* `{:staged_houdini_tag}`
* `{:start_checking_here}`
* `{:subsumption}`
* `{:template}`
* `{:terminates}`
* `{:upper}`
* `{:verified_under}`
* `{:weight}`
* `{:yields}`


