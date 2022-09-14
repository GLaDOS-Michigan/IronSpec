# 25. Dafny User's Guide {#sec-user-guide}

Most of this document describes the Dafny programming language.
This section describes the `dafny` tool, a combined verifier and compiler
that implements the Dafny language.

The development of the Dafny language and tool is a GitHub project at [https://github.com/dafny-lang/dafny](https://github.com/dafny-lang/dafny).
The project is open source, with collaborators from various organizations and additional contributors welcome.
The software itself is licensed under the [MIT license](https://github.com/dafny-lang/dafny/blob/master/LICENSE.txt).

## 25.1. Introduction

The `dafny` tool implements the following capabilities:

- checking that the input files represent a valid Dafny program (i.e., syntax, grammar and name and type resolution);
- verifying that the program meets its specifications, by translating the program to verification conditions
and checking those with Boogie and an SMT solver, typically Z3;
- compiling the program to a target language, such as C#, Java, Javascript, Go (and others in development);
- running the executable produced by the compiler.

Using various command-line flags, the tool can perform various combinations of the last three actions (the first
action is always performed).

## 25.2. Dafny Programs and Files

A Dafny program is a set of modules.
Modules can refer to other modules, such as through `import` declarations
or `refines` clauses.
A Dafny program consists of all the modules needed so that all module
references are resolved.

Dafny files (`.dfy`) in the operating system each hold
some number of top-level declarations. Thus a full program may be
distributed among multiple files.
To apply the `dafny` tool to a Dafny program, the `dafny` tool must be
given all the files making up a complete program (or, possibly, more than
one program at a time). This can be effected either by listing all of the files
by name on the command-line or by using `include` directives within a file
to stipulate what other files contain modules that the given file needs.
Thus the complete set of modules are all the modules in all the files listed
on the command-line or referenced, recursively, by `include` directives
within those files. It does not matter if files are repeated either as
includes or on the command-line.[^fn-duplicate-files]

Note however that although the complete set of files, command-line plus
included files, make up the program, by default, only those files listed on
the command-line are verified. To do a complete verification, each file
must be verified; it may well happen that a verification failure in one
file (which is not on the command-line and thus not checked) may hide a
verification failure in a file that is being checked.
Thus it is important to eventually check all files, preferably in an order
in which the files without dependencies are checked first, then those that
depend on them, etc., until all files are checked.

[^fn-duplicate-files]: File names are considered equal if they have the same absolute path, compared as case-sensitive strings (regardless of whether the underlying file-system is case sensitive).  Using symbolic links may make the same file have a different absolute path; this will generally cause duplicate declaration errors.

## 25.3. Installing Dafny

The instructions for installing dafny and the required dependencies and environment
are described on the Dafny wiki:
[https://github.com/dafny-lang/dafny/wiki/INSTALL](https://github.com/dafny-lang/dafny/wiki/INSTALL).
They are not repeated here to avoid replicating information that
easily becomes inconsistent and out of date.

As of this writing, users can install pre-built Dafny binaries
or build directly from the source files maintained in the github project.

Current and past Dafny binary releases can be found at
[https://github.com/dafny-lang/dafny/releases](https://github.com/dafny-lang/dafny/releases) for each supported platform.
Each release is a .zip file with a name combining the release name and the
platform. Current platforms are Windows 10, Ubuntu 16ff, and MacOS 10.14ff.

The principal dependency of the `dafny` tool is that it uses `dotnet`, which
is available and must be installed on Linux and Mac platforms to use `dafny`.

## 25.4. Dafny Code Style

There are code style conventions for Dafny code, recorded [here](https://dafny-lang.github.io/dafny/StyleGuide/Style-Guide).
Most significantly, code is written without tabs and with a 2 space indentation.


## 25.5. IDEs for Dafny

Dafny source files are text files and can of course be edited with any
text editor. However, some tools provide syntax-aware features:

- There is a [Dafny mode for
    Emacs](https://github.com/boogie-org/boogie-friends).

- VSCode, a cross-platform editor for many programming languages has an extension for Dafny,
  installed from within VSCode. VSCode is available [here](http://code.visualstudio.com).
  The [extension](#sec-dafny-language-server-vscode) provides syntax highlighting, in-line parser,
  type and verification errors, code navigation, counter-example display and gutter highlights.

- An old Visual Studio plugin is no longer supported

Information about installing IDE extensions for Dafny is found
on the [Dafny INSTALL page in the wiki](https://github.com/dafny-lang/dafny/wiki/INSTALL).

## 25.6. Using Dafny From the Command Line

`dafny` is a conventional command-line tool, operating just like other
command-line tools in Windows and Unix-like systems.


- The format of a command-line is determined by the shell program that is executing the command-line (.e.g. bash, the windows shell, COMMAND, etc.). The command-line typically consists of file names and options, in any order, separated by spaces.
- Files are designated by absolute paths or paths relative to the current
working directory. A command-line argument not matching a known option is considered a filepath.
- Files containing dafny code must have a `.dfy` suffix.
- There must be at least one `.dfy` file.
- The command-line may contain other kinds of files appropriate to
the language that the dafny files are being compiled to.

The command `Dafny.exe /?` gives the current set of options supported
by the tool. The most commonly used options are described in [Section 25.9](#sec-command-line-options).

- Options may begin with either a `/` (as is typical on Windows) or a `-` (as is typical on Linux)
- If an option is repeated (e.g., with a different argument), then the later instance on the command-line supersedes the earlier instance.
- If an option takes an argument, the option name is followed by a `:` and then by the argument value, with no
intervening white space; if the argument itself contains white space, the argument must be enclosed in quotes.
- Escape characters are determined by the shell executing the command-line.

The `dafny` tool performs several tasks:

- Checking the form of the text in a `.dfy` file. This step is always performed, unless the tool is simply asked for
help information or version number.
- Running the verification engine to check all implicit and explicit specifications. This step is performed by
default, but can be skipped by using the `-noVerify` or `-dafnyVerify:0` option
- Compiling the dafny program to a target language. This step is performed by default if the verification is
successful but can be skipped or always executed by using variations of the `-compile` option.
- Whether the source code of the compiled target is written out is controlled by `-spillTargetCode`
- The particular target language used is chosen by `-compileTarget`
- Whether or not the `dafny` tool attempts to run the compiled code is controlled by `-compile`

The dafny tool terminates with these exit codes:

* 0 -- success
* 1 -- invalid command-line arguments
* 2 -- syntax, parse, or name or type resolution errors
* 3 -- compilation errors
* 4 -- verification errors

Errors in earlier phases of processing typically hide later errors.
For example, if a program has parsing errors, verification or compilation will
not be attempted.

## 25.7. Verification

In this section, we suggest a methodology to figure out [why a single assertion might not hold](#sec-verification-debugging), we propose techniques to deal with [assertions that slow a proof down](#sec-verification-debugging-slow), we explain how to [verify assertions in parallel or in a focused way](#sec-assertion-batches), and we also give some more examples of [useful options and attributes to control verification](#sec-command-line-options-and-attributes-for-verification).

### 25.7.1. Verification debugging when verification fails {#sec-verification-debugging}

Let's assume one assertion is failing ("assertion might not hold" or "postcondition might not hold"). What should you do next?

The following section is textual description of the animation below, which illustrates the principle of debugging an assertion by computing the weakest precondition:  
![weakestpreconditionDemo](https://user-images.githubusercontent.com/3601079/157976402-83fe4d37-8042-40fc-940f-bcfc235c7d2b.gif)

#### 25.7.1.1. Failing postconditions {#sec-failing-postconditions}
Let's look at an example of a failing postcondition.
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    return j;
  }//^^^^^^^ a postcondition might not hold on this return path.
  i := 2;
}
```
One first thing you can do is replace the statement `return j;` by two statements `i := j; return;` to better understand what is wrong:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    i := j;
    return;
  }//^^^^^^^ a postcondition might not hold on this return path.
  i := 2;
}
```
Now, you can assert the postcondition just before the return:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    i := j;
    assert 2 <= i; // This assertion might not hold
    return;
  }
  i := 2;
}
```
That's it! Now the postcondition is not failing anymore, but the `assert` contains the error!
you can now move to the next section to find out how to debug this `assert`.

#### 25.7.1.2. Failing asserts {#sec-failing-asserts}
In the [previous section](#sec-failing-postconditions), we arrived at the point where we have a failing assertion:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    i := j;
    assert 2 <= i; // This assertion might not hold
    return;
  }
  i := 2;
}
```
To debug why this assert might not hold, we need to _move this assert up_, which is similar to [_computing the weakest precondition_](https://en.wikipedia.org/wiki/Predicate_transformer_semantics#Weakest_preconditions).
For example, if we have `x := Y; assert F;` and the `assert F;` might not hold, the weakest precondition for it to hold before `x := Y;` can be written as the assertion `assert F[x:= Y];`, where we replace every occurence of `x` in `F` into `Y`.
Let's do it in our example:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    assert 2 <= j; // This assertion might not hold
    i := j;
    assert 2 <= i;
    return;
  }
  i := 2;
}
```
Yay! The assertion `assert 2 <= i;` is not proven wrong, which means that if we manage to prove `assert 2 <= j;`, it will work.
Now, this assert should hold only if we are in this branch, so to _move the assert up_, we need to guard it.
Just before the `if`, we can add the weakest precondition `assert b ==> (2 <= j)`:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  assert b  ==>  2 <= j;  // This assertion might not hold
  if b {
    assert 2 <= j;
    i := j;
    assert 2 <= i;
    return;
  }
  i := 2;
}
```
Again, now the error is only on the topmost assert, which means that we are making progress.
Now, either the error is obvious, or we can one more time replace `j` by its value and create the assert `assert b ==> ((if !b then 3 else 1) >= 2);`
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  assert b  ==>  2 <= (if !b then 3 else 1);  // This assertion might not hold
  var j := if !b then 3 else 1;
  assert b  ==>  2 <= j;
  if b {
    assert 2 <= j;
    i := j;
    assert 2 <= i;
    return;
  }
  i := 2;
}
```
At this point, this is pure logic. We can simplify the assumption:
```
b ==>  2 <= (if !b then 3 else 1)
!b ||  (if !b then 2 <= 3 else 2 <= 1)
!b ||  (if !b then true else false)
!b || !b;
!b;
```
Now we can understand what went wrong: When b is true, all of these formulas above are false, this is why the `dafny` verifier was not able to prove them.
In the next section, we will explain how to "move asserts up" in certain useful patterns.

#### 25.7.1.3. Failing asserts cases {#sec-failing-asserts-special-cases}

This list is not exhaustive but can definitely be useful to provide the next step to figure out why Dafny could not prove an assertion.

 Failing assert           | Suggested rewriting
--------------------------|---------------------------------------
 <br>`x := Y;`<br>`assert P;` | `assert P[x := Y];`<br>`x := Y;`<br>`assert P;`
 <br>`if B {`<br>&nbsp;&nbsp;`  assert P;`<br>&nbsp;&nbsp;`  ...`<br>`}` | `assert B ==> P;`<br>`if B {`<br>&nbsp;&nbsp;`  assert P;`<br>&nbsp;&nbsp;`  ...`<br>`}`
 <br>`if B {`<br>&nbsp;&nbsp;`  ...`<br>`} else {`<br>&nbsp;&nbsp;`  assert P;`<br>&nbsp;&nbsp;`  ...`<br>`}` | `assert !B ==> P;`<br>`if B {`<br>&nbsp;&nbsp;`  ...`<br>`} else {`<br>&nbsp;&nbsp;`  assert P;`<br>&nbsp;&nbsp;`  ...`<br>`}`
 <br><br>`if X {`<br>&nbsp;&nbsp;`  ...`<br>`} else {`<br>&nbsp;&nbsp;`  ...`<br>`}`<br>`assert A;` | `if X {`<br>&nbsp;&nbsp;`  ...`<br>&nbsp;&nbsp;`  assert A;`<br>`} else {`<br>&nbsp;&nbsp;`  ...`<br>&nbsp;&nbsp;`  assert A;`<br>`}`<br>`assert A;`
 <br><br><br><br><br>`assert forall x :: Q(x);` | [`forall x`](#sec-forall-statement)<br>&nbsp;&nbsp;`  ensures Q(x)`<br>`{`<br>&nbsp;&nbsp;`  assert Q(x);`<br>`};`<br>` assert forall x :: Q(x);`
 <br><br><br><br><br>`assert forall x :: P(x) ==> Q(x);` | [`forall x | P(x)`](#sec-forall-statement)<br>&nbsp;&nbsp;`  ensures Q(x)`<br>`{`<br>&nbsp;&nbsp;`  assert Q(x);`<br>`};`<br>` assert forall x :: P(x) ==> Q(x);`
 <br>`assert exists x | P(x) :: Q(x);`<br>`assert exists x | P(x) :: Q'(x);` | `if x :| P(x) {`<br>&nbsp;&nbsp;`  assert Q(x);`<br>&nbsp;&nbsp;`  assert Q'(x);`<br>`} else {`<br>&nbsp;&nbsp;`  assert false;`<br>`}`
 <br>`assert exists x :: P(x);`<br> | `assert P(x0);`<br>`assert exists x :: P(x);`<br>for a given expression `x0`.
 <br>`ensures exists i :: P(i);`<br> | `returns (j: int)`<br>`ensures P(j) ensures exists i :: P(i)`<br>in a lemma, so that the `j` can be computed explicitly.
 <br><br>`assert A == B;`<br>`callLemma(x);`<br>`assert B == C;`<br> | [`calc == {`](#sec-calc-statement)<br>&nbsp;&nbsp;`  A;`<br>&nbsp;&nbsp;`  B;`<br>&nbsp;&nbsp;`  { callLemma(x); }`<br>&nbsp;&nbsp;`  C;`<br>`};`<br>`assert A == B;`<br>where the [`calc`](#sec-calc-statement) statement can be used to make intermediate computation steps explicit. Works with `<`, `>`, `<=`, `>=`, `==>`, `<==` and `<==>` for example.
 <br><br><br>`assert A ==> B;` | `if A {`<br>&nbsp;&nbsp;`  assert B;`<br>`};`<br>`assert A ==> B;`
 <br><br>`assert A && B;` | `assert A;`<br>`assert B;`<br>`assert A && B;`
 <br>`assert P(x);`<br>where `P` is an [`{:opaque}`](#sec-opaque) predicate | [`reveal P();`](#sec-reveal-statement)<br>`assert P(x);`<br><br>
 `assert P(x);`<br>where `P` is an [`{:opaque}`](#sec-opaque) predicate<br><br> | [`assert P(x) by {`](#sec-assert-statement)<br>[&nbsp;&nbsp;`  reveal P();`](#sec-reveal-statement)<br>`}`
 `assert P(x);`<br>where `P` is not an [`{:opaque}`](#sec-opaque) predicate with a lot of `&&` in its body and is assumed | Make `P` [`{:opaque}`](#sec-opaque) so that if it's assumed, it can be proven more easily. You can always [reveal](#sec-reveal-statement) it when needed.
 `ensures P ==> Q` on a lemma<br> | `requires P ensures Q` to avoid accidentally calling the lemma on inputs that do not satisfy `P`
 `seq(size, i => P)` | `seq(size, i requires 0 <= i < size => P);`
  <br><br>`assert forall x :: G(i) ==> R(i);` |  `assert G(i0);`<br>`assert R(i0);`<br>`assert forall i :: G(i) ==> R(i);` with a guess of the `i0` that makes the second assert to fail.
  <br><br>`assert forall i | 0 < i <= m :: P(i);` |  `assert forall i | 0 < i < m :: P(i);`<br>`assert forall i | i == m :: P(i);`<br>`assert forall i | 0 < i <= m :: P(i);`<br><br>
  <br><br>`assert forall i | i == m :: P(m);` |  `assert P(m);`<br>`assert forall i | i == m :: P(i);`
  `method m(i) returns (j: T)`<br>&nbsp;&nbsp;`  requires A(i)`<br>&nbsp;&nbsp;`  ensures B(i, j)`<br>`{`<br>&nbsp;&nbsp;`  ...`<br>`}`<br><br>`method n() {`<br>&nbsp;&nbsp;`  ...`<br><br><br>&nbsp;&nbsp;`  var x := m(a);`<br>&nbsp;&nbsp;`  assert P(x);` | `method m(i) returns (j: T)`<br>&nbsp;&nbsp;`  requires A(i)`<br>&nbsp;&nbsp;`  ensures B(i, j)`<br>`{`<br>&nbsp;&nbsp;`  ...`<br>`}`<br><br>`method n() {`<br>&nbsp;&nbsp;`  ...`<br>&nbsp;&nbsp;`  assert A(k);`<br>&nbsp;&nbsp;`  assert forall x :: B(k, x) ==> P(x);`<br>&nbsp;&nbsp;`  var x := m(k);`<br>&nbsp;&nbsp;`  assert P(x);`
  `method m_mod(i) returns (j: T)`<br>&nbsp;&nbsp;`  requires A(i)`<br>&nbsp;&nbsp;`  modifies this, i`<br>&nbsp;&nbsp;`  ensures B(i, j)`<br>`{`<br>&nbsp;&nbsp;`  ...`<br>`}`<br><br>`method n_mod() {`<br>&nbsp;&nbsp;`  ...`<br><br><br><br><br>&nbsp;&nbsp;`  var x: m_mod(a);`<br>&nbsp;&nbsp;`  assert P(x);` | `method m_mod(i) returns (j: T)`<br>&nbsp;&nbsp;`  requires A(i)`<br>&nbsp;&nbsp;`  modifies this, i`<br>&nbsp;&nbsp;`  ensures B(i, j)`<br>`{`<br>&nbsp;&nbsp;`  ...`<br>`}`<br><br>`method n_mod() {`<br>&nbsp;&nbsp;`  ...`<br>&nbsp;&nbsp;`  assert A(k);`<br>&nbsp;&nbsp;`  modify this, i; // Temporarily`<br>&nbsp;&nbsp;`  var x := T;     // Temporarily`<br>&nbsp;&nbsp;`  assume B(k, x);`<br>&nbsp;&nbsp;`//  var x := m_mod(k);`<br>&nbsp;&nbsp;`  assert P(x);`
  <br>`modify x, y;`<br>`assert P(x, y, z);` | `assert x != z && y != z;`<br>`modify x, y;`<br>`assert P(x, y, z);`

### 25.7.2. Verification debugging when verification is slow {#sec-verification-debugging-slow}

In this section, we describe techniques to apply in the case when verification is slower than expected, does not terminate, or times out.

#### 25.7.2.1. `assume false;` {#sec-assume-false}

Assuming `false` is an empirical way to short-circuit the verifier and usually stop verification at a given point[^explainer-assume-false], and since the final compilation steps do not accept this command, it is safe to use it during development.
Another similar command, `assert false;`, would also short-circuit the verifier, but it would still make the verifier try to prove `false`, which can also lead to timeouts.

[^explainer-assume-false]: `assume false` tells the `dafny` verifier "Assume everything is true from this point of the program". The reason is that, 'false' proves anything. For example, `false ==> A` is always true because it is equivalent to `!false || A`, which reduces to `true || A`, which reduces to `true`.

Thus, let us say a program of this shape takes forever to verify.

```dafny
method NotTerminating(b: bool) {
   assert X;
   if b {
     assert Y;
   } else {
     assert Z;
     assert P;
   }
}
```

What we can first do is add an `assume false` at the beginning of the method:

```dafny
method NotTerminating() {
   assume false; // Will never compile, but everything verifies instantly
   assert X;
   if b {
     assert Y;
   } else {
     assert Z;
     assert P;
   }
   assert W;
}
```

This verifies instantly. This gives use a strategy to bisect, or do binary search to find the assertion that slows everything down.
Now, we move the `assume false;` below the next assertion:

```dafny
method NotTerminating() {
   assert X;
   assume false;
   if b {
     assert Y;
   } else {
     assert Z;
     assert P;
   }
   assert W;
}
```

If verification is slow again, we can use [techniques seen before](#sec-verification-debugging) to decompose the assertion and find which component is slow to prove.

If verification is fast, that's the sign that `X` is probably not the problem,. We now move the `assume false;` after the if/then block:

```dafny
method NotTerminating() {
   assert X;
   if b {
     assert Y;
   } else {
     assert Z;
     assert P;
   }
   assume false;
   assert W;
}
```

Now, if verification is fast, we know that `assert W;` is the problem. If it is slow, we know that one of the two branches of the `if` is the problem.
The next step is to put an `assume false;` at the end of the `then` branch, and an `assume false` at the beginning of the else branch:

```dafny
method NotTerminating() {
   assert X;
   if b {
     assert Y;
     assume false;
   } else {
     assume false;
     assert Z;
     assert P;
   }
   assert W;
}
```

Now, if verification is slow, it means that `assert Y;` is the problem.
If verification is fast, it means that the problem lies in the `else` branch.
One trick to ensure we measure the verification time of the `else` branch and not the then branch is to move the first `assume false;` to the top of the then branch, along with a comment indicating that we are short-circuiting it for now.
Then, we can move the second `assume false;` down and identify which of the two assertions makes the verifier slow.


```dafny
method NotTerminating() {
   assert X;
   if b {
     assume false; // Short-circuit because this branch is verified anyway
     assert Y;
   } else {
     assert Z;
     assume false;
     assert P;
   }
   assert W;
}
```

If verification is fast, which of the two assertions `assert Z;` or `assert P;` causes the slowdown?[^answer-slowdown]

[^answer-slowdown]: `assert P;`.

We now hope you know enough of `assume false;` to locate assertions that make verification slow.
Next, we will describe some other strategies at the assertion level to figure out what happens and perhaps fix it.

#### 25.7.2.2. `assert ... by {}` {#sec-verification-debugging-assert-by}

If an assertion `assert X;` is slow, it is possible that calling a lemma or invoking other assertions can help to prove it: The postcondition of this lemma, or the added assertions, could help the `dafny` verifier figure out faster how to prove the result.

```dafny
  assert SOMETHING_HELPING_TO_PROVE_LEMMA_PRECONDITION;
  LEMMA();
  assert X;
...
lemma () 
  requires LEMMA_PRECONDITION
  ensures X { ... }
```

However, this approach has the problem that it exposes the asserted expressions and lemma postconditions not only for the assertion we want to prove faster,
but also for every assertion that appears afterwards. This can result in slowdowns[^verifier-lost].
A good practice consists of wrapping the intermediate verification steps in an `assert ... by {}`, like this:


```dafny
  assert X by {
    assert SOMETHING_HELPING_TO_PROVE_LEMMA_PRECONDITION;
    LEMMA();
  }
```

Now, only `X` is available for the `dafny` verifier to prove the rest of the method.

[^verifier-lost]: By default, the expression of an assertion or a precondition is added to the knowledge base of the `dafny` verifier for further assertions or postconditions. However, this is not always desirable, because if the verifier has too much knowledge, it might get lost trying to prove something in the wrong direction.

#### 25.7.2.3. Labeling and revealing assertions {#sec-labeling-revealing-assertions}

Another way to prevent assertions or preconditions from cluttering the verifier[^verifier-lost] is to label and reveal them.
Labeling an assertion has the effect of "hiding" its result, until there is a "reveal" calling that label.

The example of the [previous section](#sec-verification-debugging-assert-by) could be written like this.

```dafny
  assert p: SOMETHING_HELPING_TO_PROVE_LEMMA_PRECONDITION;
  // p is not available here.
  assert X by {
    reveal p;
    LEMMA();
  }
```

Similarly, if a precondition is only needed to prove a specific result in a method, one can label and reveal the precondition, like this:

```dafny
method Slow(i: int, j: int)
  requires greater: i > j {
  
  assert i >= j by {
    reveal greater;
  }
}
```

#### 25.7.2.4. Non-opaque `function method` {#sec-non-opaque-function-method}

Functions are normally used for specifications, but their functional syntax is sometimes also desirable to write application code.
However, doing so naively results in the body of a `function method Fun()` be available for every caller, which can cause the verifier to time out or get extremely slow[^verifier-lost].
A solution for that is to add the attribute [`{:opaque}`](#sec-opaque) right between `function method` and `Fun()`, and use [`reveal Fun();`](#sec-reveal-statement) in the calling functions or methods when needed.

#### 25.7.2.5. Conversion to and from bitvectors {#sec-conversion-to-and-from-bitvectors}

Bitvectors and natural integers are very similar, but they are not treated the same by the `dafny` verifier. As such, conversion from `bv8` to an `int` and vice-versa is not straightforward, and can result in slowdowns.

There are two solutions to this for now. First, one can define a [subset type](#sec-subset-types) instead of using the built-in type `bv8`:

```dafny
type byte = x | 0 <= x < 256
```

One of the problems of this approach is that additions, substractions and multiplications do not enforce the result to be in the same bounds, so it would have to be checked, and possibly truncated with modulos. For example:

```dafny
  var a: byte := 250;
  var b: byte := 200;
  var c := b - a;               // inferred to be an 'int', its value will be 50.
  var d := a + b;               // inferred to be an 'int', its value will be 450.
  var e := (a + b) % 256;       // still inferred to be an 'int'...
  var f: byte := (a + b) % 256; // OK
```

A better solution consists of creating a [newtype](#sec-newtypes) that will have the ability to check bounds of arithmetic expressions, and can actually be compiled to bitvectors as well.

```dafny
newtype {:nativeType "char"} byte = x | 0 <= x < 256
  var a: byte := 250;
  var b: byte := 200;
  var c := b - a; // OK, inferred to be a byte
  var d := a + b; // Error: cannot prove that the result of a + b is of type `byte`.
  var f := ((a as int + b as int) % 256) as byte // OK
```

One might consider refactoring this code into separate functions if used over and over.

#### 25.7.2.6. Nested loops {#sec-nested-loops}

In the case of nested loops, the verifier might timeout sometimes because of the information available[^verifier-lost].
One way to mitigate this problem, when it happens, is to isolate the inner loop by refactoring it into a separate method, with suitable pre and postconditions that will usually assume and prove the invariant again.
For example,

```dafny
`while X
   invariant Y
 {
   while X'
     invariant Y'
   {
 
   }
 }
```

could be refactored as this:

```dafny
`while X
   invariant Y
 {
   innerLoop();
 }
...
method innerLoop()
  require Y'
  ensures Y'
```

In the next section, when everything can be proven in a timely manner, we explain another strategy to decrease proof time by parallelizing it if needed, and making the verifier focus on certain parts.

### 25.7.3. Assertion batches {#sec-assertion-batches}

To understand how to control verification,
it is first useful to understand how `dafny` verifies functions and methods.

For every method (or function, constructor, etc.), `dafny` extracts _assertions_. Here is a non-exhaustive list of such extracted assertions:

**Integer assertions:**

* Every [division](#sec-numeric-types) yields an _assertion_ that the divisor is never zero.
* Every [bounded number operation](#sec-numeric-types) yields an _assertion_ that the result will be within the same bounds (no overflow, no underflows).
* Every [conversion](#sec-as-expression) yields an _assertion_ that conversion is compatible.
* Every [bitvector shift](#sec-bit-vector-types) yields an _assertion_ that the shift amount is never negative, and that the shift amount is within the width of the value.

**Object assertions:**

* Every [object property access](#sec-class-types) yields an _assertion_ that the object is not null.
* Every assignment `o.f := E;` yields an _assertion_ that `o` is among the set of objects of the `modifies` clause of the enclosing [loop](#sec-loop-framing) or [method](#sec-modifies-clause).
* Every read `o.f` yields an _assertion_ that `o` is among the set of objects of the [`reads`](#sec-reads-clause) clause of the enclosing function or predicate; or the [`modifies`](#sec-modifies-clause) clause of the enclosing method.
* Every [array access](#sec-array-types) `a[x]` yields the assertion that `0 <= x < a.Length`.
* Every [sequence access](#sec-sequences) `a[x]` yields an _assertion_, that `0 <= x < |a|`, because sequences are never null.
* Every [datatype update expression](#sec-datatype-update-suffix) and [datatype destruction](#sec-algebraic-datatype) yields an _assertion_ that the object has the given property.
* Every method overriding a [`trait`](#sec-trait-types) yields an _assertion_ that any postcondition it provides implies the postcondition of its parent trait, and an _assertion_ that any precondition it provides is implied by the precondition of its parent trait.

**Other implicit assertions:**

* Every value whose type is assigned to a [subset type](#sec-subset-types) yields an _assertion_ that it satisfies the subset type constraint.
* Every non-empty [subset type](#sec-subset-types) yields an _assertion_ that its witness satisfies the constraint.
* Every [Assign-such-that operator](#sec-update-and-call-statement) `x :| P(x)` yields an _assertion_ that `exists x :: P(x)`.
* Every recursive function yields an _assertion_ that [it terminates](#sec-loop-termination).
* Every [match expression](#sec-match-expression) or [alternative if statement](#sec-if-statement) yields an _assertion_ that all cases are covered.

**Explicit assertions:**

* Any explicit [`assert`](#sec-assert-statement) statement is _an assertion_[^precision-requires-clause].
* A consecutive pair of lines in a [`calc`](#sec-calc-statement) statement forms _an assertion_ that the expressions are related according to the common operator.
* Every call to a function or method with a [`requires`](#sec-requires-clause) clause yields _one assertion per requires clause_[^precision-requires-clause]
  (special cases such as sequence indexing come with a special `requires` clause that the index is within bounds).
* Every [`ensures`](#sec-ensures-clause) clause yields an _assertion_ at the end of the method and on every return, and on [`forall`](#sec-forall-statement) statements.
* Every [`invariant`](#sec-invariant-clause) clause yields an _assertion_ that it holds before the loop and an _assertion_ that it holds at the end of the loop.
* Every [`decreases`](#sec-decreases-clause) clause yields an _assertion_ at either a call site or at the end of a while loop.
* Every [`yield ensures`](#sec-iterator-specification) clause on an [iterator](#sec-iterator-types) yields _assertions_ that the clause holds at every yielding point.
* Every [`yield requires`](#sec-iterator-specification) clause on an [iterator](#sec-iterator-types) yields _assertions_ that the clause holds at every point when the iterator is called.


[^precision-requires-clause]: `dafny` actually breaks things down further. For example, a precondition `requires A && B` or an assert statement `assert A && B;` turns into two assertions, more or less like `requires A requires B` and `assert A; assert B;`.

It is useful to mentally visualize all these assertions as a list that roughly follows the order in the code,
except for `ensures` or `decreases` that generate assertions that seem earlier in the code but, for verification purposes, would be placed later.
In this list, each assertion depends on other assertions, statements and expressions that appear earlier in the control flow[^complexity-path-encoding].

[^complexity-path-encoding]: All the complexities of the execution paths (if-then-else, loops, goto, break....) are, down the road and for verification purposes, cleverly encoded with variables recording the paths and guarding assumptions made on each path. In practice, a second clever encoding of variables enables grouping many assertions together, and recovers which assertion is failing based on the value of variables that the SMT solver returns.

The fundamental unit of verification in `dafny` is an _assertion batch_, which consists of one or more assertions from this "list", along with all the remaining assertions turned into assumptions. To reduce overhead, by default `dafny` collects all the assertions in the body of a given method into a single assertion batch that it sends to the verifier, which tries to prove it correct.

* If the verifier says it is correct[^smt-encoding], it means that all the assertions hold.
* If the verifier returns a counterexample, this counterexample is used to determine both the failing assertion and the failing path.
  In order to retrieve additional failing assertions, `dafny` will again query the verifier after turning previously failed assertions into assumptions.[^example-assertion-turned-into-assumption] [^caveat-about-assertion-and-assumption]
* If the verifier returns `unknown` or times out, or even preemptively for difficult assertions or to reduce the chance that the verifier will ‘be confused’ by the many assertions in a large batch, `dafny` may partition the assertions into smaller batches[^smaller-batches]. An extreme case is the use of the `/vcsSplitOnEveryAssert` command-line option or the [`{:vcs_split_on_every_assert}` attribute](#sec-vcs_split_on_every_assert), which causes `dafny` to make one batch for each assertion.

[^smt-encoding]: The formula sent to the underlying SMT solver is the negation of the formula that the verifier wants to prove - also called a VC or verification condition. Hence, if the SMT solver returns "unsat", it means that the SMT formula is always false, meaning the verifier's formula is always true. On the other side, if the SMT solver returns "sat", it means that the SMT formula can be made true with a special variable assignment, which means that the verifier's formula is false under that same variable assignment, meaning it's a counter-example for the verifier. In practice and because of quantifiers, the SMT solver will usually return "unknown" instead of "sat", but will still provide a variable assignment that it couldn't prove that it does not make the formula true. `dafny` reports it as a "counter-example" but it might not be a real counter-example, only provide hints about what `dafny` knows.

[^example-assertion-turned-into-assumption]: This [post](https://github.com/dafny-lang/dafny/discussions/1898#discussioncomment-2344533) gives an overview of how assertions are turned into assumptions for verification purposes.

[^caveat-about-assertion-and-assumption]: Caveat about assertion and assumption: One big difference between an "assertion transformed in an assumption" and the original "assertion" is that the original "assertion" can unroll functions twice, whereas the "assumed assertion" can unroll them only once. Hence, `dafny` can still continue to analyze assertions after a failing assertion without automatically proving "false" (which would make all further assertions vacuous).

[^smaller-batches]: To create a smaller batch, `dafny` duplicates the assertion batch, and arbitrarily transforms the clones of an assertion into assumptions except in exactly one batch, so that each assertion is verified only in one batch. This results in "easier" formulas for the verifier because it has less to prove, but it takes more overhead because every verification instance have a common set of axioms and there is no knowledge sharing between instances because they run independently.

#### 25.7.3.1. Controlling assertion batches {#sec-assertion-batches-control}

Here is how you can control how `dafny` partitions assertions into batches.

* [`{:focus}`](#sec-focus) on an assert generates a separate assertion batch for the assertions of the enclosing block.
* [`{:split_here}`](#sec-split_here) on an assert generates a separate assertion batch for assertions after this point.
* [`{:vcs_split_on_every_assert}`](#sec-vcs_split_on_every_assert) on a function or a method generates one assertion batch per assertion

We discourage the use of the following _heuristics attributes_ to partition assertions into batches.
The effect of these attributes may vary, because they are low-level attributes and tune low-level heuristics, and will result in splits that could be manually controlled anyway.
* [`{:vcs_max_cost N}`](#sec-vcs_max_cost) on a function or method enables splitting the assertion batch until the "cost" of each batch is below N.
  Usually, you would set [`{:vcs_max_cost 0}`](#sec-vcs_max_cost) and [`{:vcs_max_splits N}`](#sec-vcs_max_splits) to ensure it generates N assertion batches.
* [`{:vcs_max_keep_going_splits N}`](#sec-vcs_max_keep_going_splits) where N > 1 on a method dynamically splits the initial assertion batch up to N components if the verifier is stuck the first time.

### 25.7.4. Command-line options and other attributes to control verification {#sec-command-line-options-and-attributes-for-verification}

There are many great options that control various aspects of verifying dafny programs. Here we mention only a few:

- Control of output: [`/dprint`](#sec-controlling-output), [`/rprint`](#sec-controlling-output), `/stats`, [`/compileVerbose`](#sec-controlling-compilation)
- Whether to print warnings: `/proverWarnings`
- Control of time: `/timeLimit`
- Control of resources: `/rLimit` and [`{:rlimit}`](#sec-rlimit)
- Control of the prover used: `/prover`
- Control of how many times to _unroll_ functions: [`{:fuel}`](#sec-fuel)

You can search for them in [this file](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef) as some of them are still documented in raw text format.

### 25.7.5. Debugging unstable verification

When evolving a Dafny codebase, it can sometimes occur that a proof
obligation succeeds at first only for the prover to time out or report a
potential error after minor, valid changes. This is ultimately due to
decidability limitations in the form of automated reasoning that Dafny
uses. The Z3 SMT solver that Dafny depends on attempts to efficiently
search for proofs, but does so using both incomplete heuristics and a
degree of randomness, with the result that it can sometimes fail to find
a proof even when one exists (or continue searching forever).

Dafny provides some features to mitigate this issue, primarily focused
on early detection. The philosophy is that, if Dafny programmers are
alerted to proofs that are starting to become unstable, before they are
obviously so, they can refactor the proofs to make them more stable
before further development becomes difficult.

The mechanism for early detection focuses on measuring the resources
used to complete a proof (either using duration or a more deterministic
"resource count" metric available from Z3). Dafny can re-run a given
proof attempt multiple times after automatically making minor changes to
the structure of the input or to the random choices made by the solver.
If the resources used during these attempts (or the ability to find a
proof at all) vary widely, we say that the verification of the relevant
properties is _unstable_.

#### 25.7.5.1. Measuring stability

To measure the stability of your proofs, start by using the
`-randomSeedIterations:N` flag to instruct Dafny to attempt each proof
goal `N` times, using a different random seed each time. The random seed
used for each attempt is derived from the global random seed `S`
specified with `-randomSeed:S`, which defaults to `0`.

For most use cases, it also makes sense to specify the
`-verificationLogger:csv` flag, to log verification cost statistics to a
CSV file. By default, the resulting CSV files will be created in the
`TestResults` folder of the current directory.

Once Dafny has completed, the
[`dafny-reportgenerator`](https://github.com/dafny-lang/dafny-reportgenerator/)
tool is a convenient way to process the output. It allows you to specify
several limits on statistics computed from the elapsed time or solver
resource use of each proof goal, returning an error code when it detects
violations of these limits. You can find documentation on the full set
of options for `dafny-reportgenerator` in its
[`README.md`](https://github.com/dafny-lang/dafny-reportgenerator/blob/main/README.md)
file.

In general, we recommend something like the following:

```
dafny-reportgenerator --max-resource-cv-pct 10 TestResults/*.csv
```

This bounds the [coefficient of
variation](https://en.wikipedia.org/wiki/Coefficient_of_variation) of
the solver resource count at 10% (0.10). We recommend a limit of less
than 20%, perhaps even as low as 5%. However, when beginning to analyze
a new project, it may be necessary to set limits as high as a few
hundred percent and incrementally ratchet down the limit over time.

When first analyzing stability, you may also find that certain proof
goals succeed on some iterations and fail on others. If your aim is
first to ensure that instability doesn't worsen and then to start
improving it, integrating `dafny-reportgenerator` into CI and using the
`--allow-different-outcomes` flag may be appropriate. Then, once you've
improved stability sufficiently, you can likely remove that flag (and
likely have significantly lower limits on other stability metrics).

#### 25.7.5.2. Improving stability

Improving stability is typically closely related to improving
performance overall. As such, [techniques for debugging slow
verification](#sec-verification-debugging-slow) are typically useful for
debugging unstable verification, as well.

## 25.8. Compilation {#sec-compilation}

The `dafny` tool can compile a Dafny program to one of several target languages. Details and idiosyncrasies of each
of these are described in the following subsections. In general note the following:

- The compiled code originating from `dafny` can be compiled with other source and binary code, but only the `dafny`-originated code is verified.
- Output file names can be set using `-out`.
- Code generated by `dafny` relies requires a Dafny-specific runtime library.  By default the runtime is included in the generated code for most languages (use `-useRuntimeLib` to omit it).  For Java and C++ the runtime must be linked to separately, except when running the generated code using `dafny`'s `-compile:3` or `-compile:4`.  All runtime libraries are part of the Binary (`./DafnyRuntime.*`) and Source (`./Source/DafnyRuntime/DafnyRuntime.*`) releases.
- Names in Dafny are written out as names in the target language. In some cases this can result in naming conflicts. Thus if a Dafny program is intended to be compiled to a target language X, you should avoid using Dafny identifiers that are not legal identifiers in X or that conflict with reserved words in X.

### 25.8.1. Main method {#sec-user-guide-main}

To generate a stand-alone executable from a Dafny program, the
Dafny program must use a specific method as the executable entry point.
That method is determined as follows:

* If the /Main option is specified on the command-line with an argument of "-", then no entry point is used at all
* If the /Main option is specified on the command-line and its argument is
not an empty string, then its argument is
interpreted as the fully-qualified name of a method to be used as the entry point. If there is no matching method, an error message is issued.
* Otherwise, the program is searched for a method with the attribute `{:main}`.
If exactly one is found, that method is used as the entry point; if more
than one method has the `{:main}` attribute, an error message is issued.
* Otherwise, the program is searched for a method with the name `Main`.
If more than one is found
an error message is issued.

Any abstract modules are not searched for candidate entry points,
but otherwise the entry point may be in any module or type. In addition,
an entry-point candidate must satisfy the following conditions:

* The method takes no parameters or type parameters
* The method is not a ghost method
* The method has no requires or modifies clauses, unless it is marked `{:main}`
* If the method is an instance (that is, non-static) method and the
  enclosing type is a class,
  then that class must not declare any constructor.
  In this case, the runtime system will
  allocate an object of the enclosing class and will invoke
  the entry-point method on it.
* If the method is an instance (that is, non-static) method and the
  enclosing type is not a class,
  then the enclosing type must, when instantiated with auto-initializing
  type parameters, be an auto-initialing type.
  In this case, the runtime system will
  invoke the entry-point method on a value of the enclosing type.

Note, however, that the following are allowed:

* The method is allowed to have `ensures` clauses
* The method is allowed to have `decreases` clauses, including a
  `decreases *`. (If Main() has a `decreases *`, then its execution may
  go on forever, but in the absence of a `decreases *` on Main(), `dafny`
  will have verified that the entire execution will eventually
  terminate.)

If no legal candidate entry point is identified, `dafny` will still produce executable output files, but
they will need to be linked with some other code in the target language that
provides a `main` entry point.

### 25.8.2. `extern` declarations {#sec-extern-decls}

A Dafny declaration can be marked with the [`{:extern}`](#sec-extern) attribute to
indicate that it refers to an external definition that is already
present in the language that the Dafny code will be compiled to (or will
be present by the time the final target-language program is compiled or
run).

Because the [`{:extern}`](#sec-extern) attribute controls interaction with code written
in one of many languages, it has some language-specific behavior,
documented in the following sections. However, some aspects are
target-language independent and documented here.

The attribute can also take several forms, each defining a different
relationship between a Dafny name and a target language name. In the
form [`{:extern}`](#sec-extern), the name of the external definition is
assumed to be the name of the Dafny declaration after some
target-specific name mangling. However, because naming conventions (and
the set of allowed identifiers) vary between languages, Dafny allows
additional forms for the `{:extern}` attribute.

The form `{:extern <s1>}` instructs `dafny` to compile references to most
declarations using the name `s1` instead of the Dafny name. For [opaque
types](#sec-opaque-types), however, `s1` is sometimes used as a hint as
to how to declare that type when compiling. This hint is interpreted
differently by each compiler.

Finally, the form `{:extern <s1>, <s2>}` instructs `dafny` to use `s2` as
the direct name of the declaration. `dafny` will typically use a
combination of `s1` and `s2`, such as `s1.s2`, to reference the
declaration. It may also be the case that one of the arguments is simply
ignored, depending on the target language.

The recommended style is to prefer `{:extern}` when possible, and use
similar names across languages. This is usually feasible because
existing external code is expected to have the same interface as the
code that `dafny` would generate for a declaration of that form. Because
many Dafny types compile down to custom types defined in the Dafny
runtime library, it's typically necessary to write wrappers by hand that
encapsulate existing external code using a compatible interface, and
those wrappers can have names chosen for compatibility. For example,
retrieving the list of command line arguments when compiling to C\#
requires a wrapper such as the following:

``` cs
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

namespace Externs_Compile {
  public partial class __default {
    public static Dafny.ISequence<icharseq> GetCommandLineArgs() {
      var dafnyArgs = Environment
                      .GetCommandLineArgs()
                      .Select(charseq.FromString);
      return Dafny.Sequence<icharseq>.FromArray(dafnyArgs.ToArray());
    }
}
```

Note that `dafny` does not check the arguments to `{:extern}`, so it is
the user's responsibility to ensure that the provided names result in
code that is well-formed in the target language.

Most declarations, including those for modules, classes, traits, member
variables, constructors, methods, function methods, and opaque types,
can be marked with `{:extern}`.

Marking a module with `{:extern}` indicates that the declarations
contained within can be found within the given module, namespace, or
similar construct within the target language. Some members of the Dafny
module may contain definitions, in which case code for those definitions
will be generated. Whether this results in valid target code may depend
on some target language support for something resembling "partial"
modules, where different subsets of the contents are defined in
different places.

The story for classes is similar. Code for a class will be generated
if any of its members are not `{:extern}`. Depending on the target
language, making either all or none of the members `{:extern}` may be
the only options that result in valid target code. Traits with
`{:extern}` can refer to existing traits or interfaces in the target
language, or can refer to the interfaces of existing classes.

Member variables marked with `{:extern}` refer to fields or properties
in existing target-language code. Constructors, methods, and function
methods refer to the equivalent concepts in the target language. They
can have contracts, which are then assumed to hold for the existing
target-language code. They can also have bodies, but the bodies will not
be compiled in the presence of the `{:extern}` attribute. Bodies can
still be used for reasoning, however, so may be valuable in some cases,
especially for function methods.

Types marked with `{:extern}` must be opaque. The name argument, if any,
usually refers to the type name in the target language, but some
compilers treat it differently.

### 25.8.3. C\#

TO BE WRITTEN

### 25.8.4. Java

The Dafny-to-Java compiler writes out the translated files of a file _A_`.dfy`
to a directory _A_-java. The `-out` option can be used to choose a
different output directory. The file _A_`.dfy` is translated to _A_`.java`,
which is placed in the output directory along with helper files.
If more than one `.dfy` file is listed on the command-line, then the output
directory name is taken from the first file, and `.java` files are written
for each of the `.dfy` files.

TO BE WRITTEN

### 25.8.5. Javascript

TO BE WRITTEN

### 25.8.6. Go

TO BE WRITTEN

### 25.8.7. C++

The C++ backend was written assuming that it would primarily support writing
C/C++ style code in Dafny, which leads to some limitations in the current
implementation.

- We do not support BigIntegers, so do not use `int`, or raw instances of
  `arr.Length`, or sequence length, etc. in executable code.  You can however,
  use `arr.Length as uint64` if you can prove your array is an appropriate
  size.  The compiler will report inappropriate integer use.
- We do not support more advanced Dafny features like traits or co-inductive
  types.
- Very limited support for higher order functions even for array init.  Use
  extern definitions like newArrayFill (see 
  [extern.dfy](https://github.com/dafny-lang/dafny/blob/master/Test/c++/extern.dfy)) or
  similar.  See also the example in [`functions.dfy`]
  (https://github.com/dafny-lang/dafny/blob/master/Test/c++/functions.dfy).
- The current backend also assumes the use of C++17 in order to cleanly and
  performantly implement datatypes.

### 25.8.8. Supported features by target language

Some Dafny features are not supported by every target language.
The table below shows which features are supported by each backend.
An empty cell indicates that a feature is not supported,
while an X indicates that it is.

{% include_relative Features.md %}

## 25.9. Dafny Command Line Options {#sec-command-line-options}

There are many command-line options to the `dafny` tool.
The most current documentation of the options is within the tool itself,
using the `/?` or `/help` option.

Remember that options can be stated with either a leading `/` or a leading `-`.

### 25.9.1. Help and version information {#sec-controlling-help}

These options select output including documentation on command-line
options or attribute declarations, information on the version of Dafny
being used, and information about how Dafny was invoked.

* `-?` or `-help` - print out the current list of command-line options
  and terminate. All of these options are also described in this and
  the following sections.

* `-attrHelp` - print out the current list of supported attribute
  declarations and terminate.

* `-version` - print the version of the executable being invoked and
  terminate.

* `-env:<n>` - print the command-line arguments supplied to the program.
  The value of `<n>` can be one of the following.

  * `0` - never print command-line arguments.

  * `1` (default) - print them to Boogie (`.bpl`) files and prover logs.

  * `2` - operate like with option `1` but also print to standard output.

* `-wait` - wait for the user to press `Enter` before terminating after a successful execution.

### 25.9.2. Controlling input {#sec-controlling-input}

These options control how Dafny processes its input.

* `-dprelude:<file>` - select an alternative Dafny prelude file. This
  file contains Boogie definitions (including many axioms) required by
  the translator from Dafny to Boogie. Using an alternative prelude is
  primarily useful if you're extending the Dafny language or changing
  how Dafny constructs are modeled. The default prelude is here:

  <https://github.com/dafny-lang/dafny/blob/master/Source/Dafny/DafnyPrelude.bpl>

* `-stdin` - read standard input and treat it as Dafny source code,
  instead of reading from a file.

### 25.9.3. Controlling plugins {#sec-controlling-plugins}

TO BE WRITTEN

### 25.9.4. Controlling output {#sec-controlling-output}

These options instruct Dafny to print various information about your
program during processing, including variations of the original source
code (which can be helpful for debugging).

* `-stats` - print various statistics about the Dafny files supplied on
  the command line. The statistics include the number of total
  functions, recursive functions, total methods, ghost methods, classes,
  and modules. They also include the maximum call graph width and the
  maximum module height.

* `-dprint:<file>` - print the Dafny program after parsing (use `-` for
  `<file>` to print to the console).

* `-rprint:<file>` - print the Dafny program after type resolution (use
  `-` for `<file>` to print to the console).

* `-printMode:<Everything|DllEmbed|NoIncludes|NoGhost>` - select what to
  include in the output requested by `-dprint` or `-rprint`. The
  argument can be one of the following.

  * `Everything` (default) - include everything.

  * `DllEmbed`- print the source that will be included in a compiled DLL.

  * `NoIncludes` - disable printing of methods incorporated via the
    include mechanism that have the `{:verify false}` attribute, as well
    as datatypes and fields included from other files.

  * `NoGhost` - disables printing of functions, ghost methods, and proof
    statements in implementation methods. Also disable anything
    `NoIncludes` disables.

* `-printIncludes:<None|Immediate|Transitive>` - select what information
  from included files to incorporate into the output selected by
  `-dprint` or `-rprint`. The argument can be one of the following.

  * `None` (default) - don't print anything from included files.

  * `Immediate` - print files directly included by files specified on
    the command line. Exit after printing.

  * `Transitive` - print files transitively included by files specified
    on the command line. Exit after printing.

* `-view:<view1, view2>` - TO BE WRITTEN

* `-funcCallGraph` - print out the function call graph. Each line has
  the format `func,mod=callee*`, where `func` is the name of a function,
  `mod` is the name of its containing module, and `callee*` is a
  space-separated list of the functions that `func` calls.

* `-showSnippets:<n>` - show a source code snippet for each Dafny
  message. The value of `<n>` can be one of the following.

  * `0` (default) - don't print snippets.

  * `1` - do print snippets.

* `-printTooltips` - dump additional positional information (displayed
  as mouse-over tooltips by LSP clients) to standard output as `Info`
  messages.

* `-pmtrace` - print debugging information from the pattern-match
  compiler.

* `-titrace` - print debugging information during the type inference
  process.

* `-diagnosticsFormat:<text|json>` - control how to report errors, warnings, and info
  messages.  `<fmt>` may be one of the following:

  * `text` (default): Report diagnostics in human-readable format.
  * `json`: Report diagnostics in JSON format, one object per diagnostic, one
    diagnostic per line.  Info-level messages are only included with
    `-printTooltips`.  End positions are only included with `-showSnippets:1`.
    Diagnostics are the following format (but without newlines):

    ```json
    {
      "location": {
        "filename": "xyz.dfy",
        "range": { // Start and (optional) end of diagnostic
          "start": {
            "pos": 83, // 0-based character offset in input
            "line": 6, // 1-based line number
            "character": 0 // 0-based column number
          },
          "end": { "pos": 86, "line": 6, "character": 3 }
        }
      },
      "severity": 2, // 1: error; 2: warning; 4: info
      "message": "module-level const declarations are always non-instance ...",
      "source": "Parser",
      "relatedInformation": [ // Additional messages, if any
        {
          "location": { ... }, // Like above
          "message": "...",
        }
      ]
    }
    ```

### 25.9.5. Controlling language features {#sec-controlling-language}

These options allow some Dafny language features to be enabled or
disabled. Some of these options exist for backward compatibility with
older versions of Dafny.

* `-noIncludes` - ignore `include` directives in the program.

* `-noExterns` - ignore `extern` and `dllimport` attributes in the
  program.

* `-functionSyntax:<version>` - select what function syntax to
  recognize. The syntax for functions is changing from Dafny version 3
  to version 4. This switch gives early access to the new syntax, and
  also provides a mode to help with migration. The valid arguments
  include the following.

  * `3` (default) - compiled functions are written `function method` and
    `predicate method`. Ghost functions are written `function` and
    `predicate`.

  * `4` - compiled functions are written `function` and `predicate`.
    Ghost functions are written `ghost function` and `ghost predicate`.

  * `migration3to4` - compiled functions are written `function method`
    and `predicate method`. Ghost functions are written `ghost function`
    and `ghost predicate`. To migrate from version 3 to version 4, use
    this flag on your version 3 program to flag all occurrences of
    `function` and `predicate` as parsing errors. These are ghost
    functions, so change those into the new syntax `ghost function` and
    `ghost predicate`. Then, start using `-functionSyntax:4`. This will
    flag all occurrences of `function method` and `predicate method` as
    parsing errors. So, change those to just `function` and `predicate`.
    As a result, your program will use version 4 syntax and have the
    same meaning as your previous version 3 program.

  * `experimentalDefaultGhost` - like `migration3to4`, but allow
    `function` and `predicate` as alternatives to declaring ghost
    functions and predicates, respectively

  * `experimentalDefaultCompiled` - like `migration3to4`, but allow
    `function` and `predicate` as alternatives to declaring compiled
    functions and predicates, respectively

  * `experimentalPredicateAlwaysGhost` - compiled functions are written
    `function`. Ghost functions are written `ghost function`. Predicates
    are always ghost and are written `predicate`.

* `-quantifierSyntax:<version>` - select what quantifier syntax to recognize.
    The syntax for quantification domains is changing from Dafny version 3 to version 4,
    more specifically where quantifier ranges (`| <Range>`) are allowed.
    This switch gives early access to the new syntax.

    * `3` (default) - Ranges are only allowed after all quantified variables are declared.
        (e.g. `set x, y | 0 <= x < |s| && y in s[x] && 0 <= y :: y`)
    * `4` - Ranges are allowed after each quantified variable declaration.
        (e.g. `set x | 0 <= x < |s|, y <- s[x] | 0 <= y :: y`)

    Note that quantifier variable domains (`<- <Domain>`) are available
    in both syntax versions.

* `-disableScopes` - treat all export sets as `export reveal *` to never
    hide function bodies or type definitions during translation.

* `-allowsGlobals` - allow the implicit class `_default` to contain
  fields, instance functions, and instance methods. These class members
  are declared at the module scope, outside of explicit classes. This
  command-line option is provided to simplify a transition from the
  behavior in the language prior to version 1.9.3, from which point
  onward all functions and methods declared at the module scope are
  implicitly static and field declarations are not allowed at the
  module scope.

### 25.9.6. Controlling warnings {#sec-controlling-warnings}

These options control what warnings Dafny produces, and whether to treat
warnings as errors.

* `-warnShadowing` - emit a warning if the name of a declared variable
  caused another variable to be shadowed.

* `-deprecation:<n>` - control warnings about deprecated features. The
  value of `<n>` can be any of the following.

   * `0` - don't issue any warnings.

   * `1` (default) - issue warnings.

   * `2` - issue warnings and advise about alternate syntax.

* `-warningsAsErrors` - treat warnings as errors.

### 25.9.7. Controlling verification {#sec-controlling-verification}

These options control how Dafny verifies the input program, including
how much it verifies, what techniques it uses to perform verification,
and what information it produces about the verification process.

* `-dafnyVerify:<n>` - turn verification of the program on or off. The
  value of `<n>` can be any of the following.

  * `0` - stop after type checking.

  * `1` - continue on to verification and compilation.

* `-verifyAllModules` - verify modules that come from include directives.

  By default, Dafny only verifies files explicitly listed on the command
  line: if `a.dfy` includes `b.dfy`, a call to `Dafny a.dfy` will detect
  and report verification errors from `a.dfy` but not from `b.dfy`.

  With this flag, Dafny will instead verify everything: all input
  modules and all their transitive dependencies. This way `Dafny a.dfy`
  will verify `a.dfy` and all files that it includes (here `b.dfy`), as
  well all files that these files include, etc.

  Running Dafny with `-verifyAllModules` on the file containing your
  main result is a good way to ensure that all its dependencies verify.

* `-separateModuleOutput` - output verification results for each module
  separately, rather than aggregating them after they are all finished.

* `-verificationLogger:<configuration string>` - log verification
  results to the given test result logger. The currently supported
  loggers are `trx`, `csv`, and `text`. These are the XML-based formats
  commonly used for test results for .NET languages, a custom CSV
  schema, and a textual format meant for human consumption,
  respectively. You can provide configuration using the same string
  format as when using the `--logger` option for dotnet test, such as:

        -verificationLogger:trx;LogFileName=<...>

  The exact mapping of verification concepts to these formats is
  experimental and subject to change!

  The `trx` and `csv` loggers automatically choose an output file name
  by default, and print the name of this file to the console. The `text`
  logger prints its output to the console by default, but can send
  output to a file given the `LogFileName` option.

  The `text` logger also includes a more detailed breakdown of what
  assertions appear in each assertion batch. When combined with the
  `-vcsSplitOnEveryAssert` option, it will provide approximate time and
  resource use costs for each assertion, allowing identification of
  especially expensive assertions.

* `-mimicVerificationOf:<dafny version>` - let `dafny` attempt to mimic
  the verification behavior of a previous version of `dafny`. This can be
  useful during migration to a newer version of `dafny` when a Dafny
  program has proofs, such as methods or lemmas, that are unstable in
  the sense that their verification may become slower or fail altogether
  after logically irrelevant changes are made in the verification input.

  Accepted versions are: `3.3`. Note that falling back on the behavior
  of version 3.3 turns off features that prevent certain classes of
  verification instability.

* `-noCheating:<n>` - control whether certain assumptions are allowed.
  The value of `<n>` can be one of the following.

  * `0` (default) - allow `assume` statements and free invariants.

  * `1` - treat all assumptions as `assert` statements, and drop free
    invariants.

* `-induction:<n>` - control the behavior of induction. The value of
  `<n>` can be one of the following.

  * `0` - never do induction, not even when attributes request it.

  * `1` - apply induction only when attributes request it.

  * `2` - apply induction as requested (by attributes) and also for
    heuristically chosen quantifiers.

  * `3` - apply induction as requested, and for heuristically chosen
    quantifiers and lemmas.

  * `4` (default) - apply induction as requested, and for all lemmas.

* `-inductionHeuristic:<n>` - control the heuristics used for induction.
  The value of `<n>` can be one of the following.

  * `0` - use the least discriminating induction heuristic (that is,
    lean toward applying induction more often).

  * `1`, `2`, `3`, `4`, `5` - use an intermediate heuristic, ordered as
    follows as far as how discriminating they are: 0 < 1 < 2 < (3,4) < 5
    < 6.

  * `6` (default) - use the most discriminating induction heuristic.

* `-trackPrintEffects:<n>` - control what implementations are allowed to
  use `print`. The value of `<n>` can be one of the following.

  * `0` (default) - every compiled method, constructor, and iterator,
    whether or not it bears a `{:print}` attribute, may have print
    effects.

  * `1` - A compiled method, constructor, or iterator is allowed to have
    print effects only if it is marked with the `{:print}` attribute.

* `-allocated:<n>` - specify defaults for where Dafny should assert and
  assume `allocated(x)` for various parameters `x`, local variables `x`,
  bound variables `x`, etc. Lower `<n>` may require more manual
  `allocated(x)` annotations and thus may be more difficult to use. The
  value of `<n>` can be one of the following.

  * `0` - never assume or assert `allocated(x)` by default.

  * `1` - assume `allocated(x)` only for non-ghost variables and fields.
    (These assumptions are free, since non-ghost variables always
    contain allocated values at run-time.) This option may speed up
    verification relative to `-allocated:2`.

  * `2` - assert/assume `allocated(x)` on all variables, even bound
    variables in quantifiers. This option is the easiest to use for code
    that uses the heap heavily.

  * `3` - (default) make frugal use of heap parameters.

  * `4` - like `3` but add `allocated` antecedents when ranges don't imply
    allocatedness.

  Warning: this option should be chosen consistently across an entire
  project; it would be unsound to use different defaults for different
  files or modules within a project. Furthermore, modes `-allocated:0` and
  `-allocated:1` let functions depend on the allocation state, which is
  not sound in general.

* `-definiteAssignment:<n>` - control the rules governing definite
  assignment, the property that every variable is eventually assigned a
  value along every path. The value of `<n>` can be one of the
  following.

  * `0` - ignore definite-assignment rules; this mode is unsound and is
    for testing only.

  * `1` (default) - enforce definite-assignment rules for compiled
    variables and fields whose types do not support auto-initialization
    and for ghost variables and fields whose type is possibly empty.

  * `2` - enforce definite-assignment for all non-yield-parameter
    variables and fields, regardless of their types.

  * `3` - like `2`, but also performs checks in the compiler that no
    nondeterministic statements are used; thus, a program that passes at
    this level 3 is one that the language guarantees that values seen
    during execution will be the same in every run of the program.

* `-noAutoReq` - ignore `autoReq` attributes, and therefore do not
  automatically generate `requires` clauses.

* `-autoReqPrint:<file>` - print the requires clauses that were
  automatically generated by `autoReq` to the given `<file>`.

* `-noNLarith` - reduce Z3's knowledge of non-linear arithmetic (the
  operators `*`, `/`, and `%`). Enabling this option will typically
  require more manual work to complete proofs (by explicitly applying
  lemmas about non-linear operators), but will also result in more
  predictable behavior, since Z3 can sometimes get stuck down an
  unproductive path while attempting to prove things about those
  operators. (This option will perhaps be replaced by `-arith` in the
  future. For now, it takes precedence over `-arith`.)

* `-arith:<n>` - control how arithmetic is modeled during verification.
  This is an experimental switch, and its options may change. The value
  of `<n>` can be one of the following.

  * `0` - use Boogie/Z3 built-ins for all arithmetic operations.

  * `1` (default) - like `0`, but introduce symbolic synonyms for `*`,
    `/`, and `%`, and allow these operators to be used in triggers.

  * `2` - like `1`, but also introduce symbolic synonyms for `+` and
    `-`.

  * `3` - turn off non-linear arithmetic in the SMT solver. Still use
    Boogie/Z3 built-in symbols for all arithmetic operations.

  * `4` - like `3`, but introduce symbolic synonyms for `*`, `/`, and `%`,
    and allow these operators to be used in triggers.

  * `5` - like `4`, but also introduce symbolic synonyms for `+` and
    `-`.

  * `6` - like `5`, and introduce axioms that distribute `+` over `*`.

  * `7` - like `6`, and introduce facts about the associativity of
    literal arguments over `*`.

  * `8` - like `7`, and introduce axioms for the connection between `*`,
    `/`, and `%`.

  * `9` - like `8`, and introduce axioms for sign of multiplication.

  * `10` - like `9`, and introduce axioms for commutativity and
    associativity of `*`.

* `-autoTriggers:<n>` - control automatic generation of `{:trigger}`
  annotations. See [triggers](#sec-trigger). The value of `<n>` can be one
  of the following.

  * `0` - do not generate `{:trigger}` annotations for user-level
    quantifiers.

  * `1` (default) - add a `{:trigger}` annotation to each user-level
    quantifier. Existing annotations are preserved.

* `-rewriteFocalPredicates:<n>` - control rewriting of predicates in the
  body of prefix lemmas. See [the section about nicer extreme proofs](#sec-nicer-proofs-of-extremes).
  The value of `<n>` can be one of the following.

  * `0` - don't rewrite predicates in the body of prefix lemmas.

  * `1` (default) - in the body of prefix lemmas, rewrite any use of a
    focal predicate `P` to `P#[_k-1]`.

* `-extractCounterexample` - control generation of counterexamples. If
  verification fails, report a detailed counterexample for the first
  failing assertion. Requires specifying the `-mv` option, to specify
  where to write the counterexample, as well as the
  `-proverOpt:O:model_compress=false` and
  `-proverOpt:O:model.completion=true` options.

* `-countVerificationErrors:<n>` - if `0` then always exit with a 0 exit
  code, regardless of whether errors are found. If `1` (default) then
  use the appropriate exit code. This option is deprecated.

### 25.9.8. Controlling Boogie {#sec-controlling-boogie}

Dafny builds on top of Boogie, a general-purpose intermediate language
for verification. Options supported by Boogie on its own are also
supported by Dafny. Some of the Boogie options most relevant to Dafny
users include the following. We use the term "procedure" below to refer
to a Dafny function, lemma, method, or predicate, following Boogie
terminology.

* `-proc:<name>` - verify only the procedure named `<name>`. The name
  can include `*` to indicate arbitrary sequences of characters.

* `-trace` - print extra information during verification, including
  timing, resource use, and outcome for each procedure incrementally, as
  verification finishes.

* `-randomSeed:<n>` - turn on randomization of the input that Boogie
  passes to the SMT solver and turn on randomization in the SMT solver
  itself.

  Certain Boogie inputs are unstable in the sense that changes to the
  input that preserve its meaning may cause the output to change. The
  `-randomSeed`` option simulates meaning-preserving changes to the
  input without requiring the user to actually make those changes.

  The `-randomSeed` option is implemented by renaming variables and
  reordering declarations in the input, and by setting
  solver options that have similar effects.

* `-randomSeedIterations:<n>` - attempt to prove each VC `<n>` times
  with `<n>` random seeds. If `-randomSeed` has been provided, each
  proof attempt will use a new random seed derived from this original
  seed. If not, it will implicitly use `-randomSeed:0` to ensure a
  difference between iterations. This option can be very useful for
  identifying input programs for which verification is unstable. If the
  verification times or solver resource counts associated with each
  proof attempt vary widely for a given procedure, small changes to that
  procedure might be more likely to cause proofs to fail in the future.

* `-vcsSplitOnEveryAssert` - prove each (explicit or implicit) assertion
  in each procedure separately. See also the attribute
  [`{:vcs_split_on_every_assert}`](#sec-vcs_split_on_every_assert) for
  restricting this option on specific procedures. By default, Boogie
  attempts to prove that every assertion in a given procedure holds all
  at once, in a single query to an SMT solver. This usually performs
  well, but sometimes causes the solver to take longer. If a proof that
  you believe should succeed is timing out, using this option can
  sometimes help.

* `-vcsCores:<n>` - try to verify `<n>` procedures simultaneously.
  Setting `<n>` to the number of physical cores available tends to be
  effective at speeding up overall proof time.

* `-timeLimit:<n>` - spend at most `<n>` seconds attempting to prove any
  single SMT query. This setting can also be set per method using the
  attribute [`{:timeLimit n}`](#sec-time-limit).

* `-rlimit:<n>` - set the maximum solver resource count to use while
  proving a single SMT query. This can be a more deterministic approach
  than setting a time limit. To choose an appropriate value, please
  refer to the documentation of the attribute [`{:rlimit}`](#sec-rlimit)
  that can be applied per procedure.

* `-print:<file>` - print the translation of the Dafny file to a Boogie file.

If you have Boogie installed locally, you can run the printed Boogie file with the following script:

```
DOTNET=$(which dotnet)

BOOGIE_ROOT="path/to/boogie/Source"
BOOGIE="$BOOGIE_ROOT/BoogieDriver/bin/Debug/net6.0/BoogieDriver.dll"

if [[ ! -x "$DOTNET" ]]; then
    echo "Error: Dafny requires .NET Core to run on non-Windows systems."
    exit 1
fi

#Uncomment if you prefer to use the executable instead of the DLL
#BOOGIE=$(which boogie)

BOOGIE_OPTIONS="/infer:j"
PROVER_OPTIONS="\
  /proverOpt:O:auto_config=false \
  /proverOpt:O:type_check=true \
  /proverOpt:O:smt.case_split=3 \
  /proverOpt:O:smt.qi.eager_threshold=100 \
  /proverOpt:O:smt.delay_units=true \
  /proverOpt:O:smt.arith.solver=2 \
  "

"$DOTNET" "$BOOGIE" $BOOGIE_OPTIONS $PROVER_OPTIONS "$@"
#Uncomment if you want to use the executable instead of the DLL
#"$BOOGIE" $BOOGIE_OPTIONS $PROVER_OPTIONS "$@"
```

### 25.9.9. Controlling the prover {#sec-controlling-prover}

TO BE WRITTEN

### 25.9.10. Controlling test generation {#sec-controlling-test-gen}

TO BE WRITTEN

### 25.9.11. Controlling compilation {#sec-controlling-compilation}

These options control what code gets compiled, what target language is
used, how compilation proceeds, and whether the compiled program is
immediately executed.

* `-compile:<n>` - control whether compilation happens. The value of
  `<n>` can be one of the following. Note that if the program is 
   compiled, it will be compiled to the target language determined by
   the `-compileTarget` option, which is C\# by default.

   * `0` - do not compile the program

   * `1` (default) - upon successful verification, compile the program
     to the target language.

   * `2` - always compile, regardless of verification success.

   * `3` - if verification is successful, compile the program (like
     option `1`), and then if there is a `Main` method, attempt to run the
     program.

   * `4` - always compile (like option `2`), and then if there is a
     `Main` method, attempt to run the program.

* `-compileTarget:<s>` - set the target programming language for the
  compiler. The value of `<s>` can be one of the following.

   * `cs` - C\# . Produces a .dll file that can be run using `dotnet`.
      For example, `dafny Hello.dfy` will produce `Hello.dll` and `Hello.runtimeconfig.json`.
      The dll can be run using `dotnet Hello.dll`.

   * `go` - Go. The default output of `dafny Hello.dfy -compileTarget:go` is
      in the `Hello-go` folder. It is run using
      ``GOPATH=`pwd`/Hello-go/ GO111MODULE=auto go run Hello-go/src/Hello.go``

   * `js` - Javascript. The default output of `dafny Hello.dfy -compileTarget:js` is
      the file `Hello.js`, which can be run using `node Hello.js`. (You must have 
      `bignumber.js` installed.)

   * `java` - Java. The default output of `dafny Hello.dfy -compileTarget:java` is
      in the `Hello-java` folder. The compiled program can be run using
      `java -cp Hello-java:Hello-java/DafnyRuntime.jar Hello`.

   * `py` - Python. The default output of `dafny Hello.dfy -compileTarget:py` is
      in the `Hello-py` folder. The compiled program can be run using
      `python Hello-py/Hello.py`, where `python` is Python version 3.

   * `cpp` - C++. The default output of `dafny Hello.dfy -compileTarget:cpp` is
      `Hello.exe` and other files written to the current folder. The compiled
      program can be run using `./Hello.exe`.


* `-spillTargetCode:<n>` - control whether to write out compiled code in
  the target language (instead of just holding it in internal temporary
  memory). The value of `<n>` can be one of the following.

   * `0` (default) - don't make any extra effort to write the textual
     target program (but still compile it, if `-compile` indicates to do
     so).

   * `1` - write it out to the target language, if it is being compiled.

   * `2` - write the compiled program if it passes verification,
     regardless of the `-compile` setting.

   * `3` - write the compiled program regardless of verification success
     and the `-compile` setting.

Note that some compiler targets may (always or in some situations) write
out the textual target program as part of compilation, in which case
`-spillTargetCode:0` behaves the same way as `-spillTargetCode:1`.

* `-Main:<name>` - specify the (fully-qualified) name of the method to
  use as the executable entry point. The default is the method with the
  `{:main}` attribute, or else the method named `Main`.

* `-out:<file>` - set the name to use for compiled code files.

By default, `dafny` reuses the name of the Dafny file being compiled.
Compilers that generate a single file use the file name as-is (e.g. the
C# backend will generate `<file>.dll` and optionally `<file>.cs` with
`-spillTargetCode`). Compilers that generate multiple files use the file
name as a directory name (e.g. the Java backend will generate files in
directory `<file>-java/`). Any file extension is ignored, so
`-out:<file>` is the same as `-out:<file>.<ext>` if `<file>` contains no
periods.

* `-compileVerbose:<n>` - control whether to write out compilation
  progress information. The value of `<n>` can be one of the following.

  * `0` - do not print any information (silent mode)

  * `1` (default) - print information such as the files being created by
    the compiler

* `-coverage:<file>` - emit branch-coverage calls and outputs into
  `<file>`, including a legend that gives a description of each
  source-location identifier used in the branch-coverage calls. (Use `-`
  as `<file>` to print to the console.)

* `-optimize` - produce optimized C# code by passing the `/optimize`
  flag to the `csc` executable.

* `-optimizeResolution:<n>` - control optimization of method target
  resolution. The value of `<n>` can be one of the following.

  * `0` - resolve and translate all methods.

  * `1` - translate methods only in the call graph of the current
    verification target.

  * `2` (default) - as in `1`, but resolve only methods that are defined
    in the current verification target file, not in included files.

* `-useRuntimeLib` - refer to the pre-built `DafnyRuntime.dll` in the
  compiled assembly rather than including `DafnyRuntime.cs` in the build
  process.

