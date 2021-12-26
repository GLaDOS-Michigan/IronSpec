<p></p> <!-- avoids duplicate title -->

# Modules

## Introduction

Structuring a program by breaking it into parts is an important part of creating large programs.
In Dafny, this is accomplished via *modules*. Modules provide a way to
group together related types, classes, methods, functions, and other modules together, as well as control the scope of
declarations.
Modules may import each other for code reuse, and it is possible to abstract over modules to seperate an implementation
from an interface.


## Declaring New Modules


A new module is declared with the `module` keyword, followed by the name of the new module, and a
pair of curly braces (`{}`) enclosing the body of the module:

```
module Mod {
  ...
}
```

A module body can consist of anything that you could put at the toplevel. This includes classes, datatypes, types, methods, functions, etc.

``` {.edit}
module Mod {
  class C {
    var f: int;
    method m()
  }
  datatype Option = A(int) | B(int)
  type T
  method m()
  function f(): int
}
```

You can also put a module inside another, in a nested fashion:

``` {.edit}
module Mod {
  module Helpers {
    class C {
      method doIt()
      var f: int;
    }
  }
}
```

Then you can refer the the members of the `Helpers` module within the `Mod`
module by prefixing them with "`Helpers.`". For example:

``` {.editonly}
module Mod {
  module Helpers {
    class C {
      method doIt()
      var f: int;
    }
  }
  method m() {
    var x := new Helpers.C;
    x.doIt();
    x.f := 4;
  }
}
```

```
module Mod {
  module Helpers { ... }
  method m() {
    var x := new Helpers.C;
    x.doIt();
    x.f := 4;
  }
}
```

Methods and functions defined at the module level are available like classes, with just the module
name prefixing them. They are also available in the methods and functions of the classes in the same module.

``` {.edit}
module Mod {
  module Helpers {
    function method addOne(n: nat): nat {
      n + 1
    }
  }
  method m() {
    var x := 5;
    x := Helpers.addOne(x); // x is now 6
  }
}
```

By default, definitions of functions (and predicates) are exposed outside of
the module they are defined in. This can be controlled more precisely with
export sets, as we will see in the following section. So adding

``` {.editonly}
module Mod {
  module Helpers {
    function method addOne(n: nat): nat {
      n + 1
    }
  }
  method m() {
    var x := 5;
    x := Helpers.addOne(x);
    assert x == 6; // this will succeed
  }
}
```

```
  assert x == 6;
```

to the end of `m()` will verify.

## Importing and Exporting Modules

Declaring new submodules is useful, but sometimes you want to refer to things from an existing module,
such as a library. In this case, you can *import* one module into another. This is done via the `import`
keyword, and there are a few different forms, each of which has a different meaning.
The simplest kind is the *concrete import*, and has the form `import A = B`. This declaration creates a reference to the module B
(which must already exist), and binds it to the new name A. Note this new name, i.e. `A`, is only bound in the
module containing the `import` declaration; it does not create a global alias. For example, if `Helpers` was
defined outside of `Mod`, then we could import it:

``` {.editonly}
module Helpers {
  function method addOne(n: nat): nat
  {
    n + 1
  }
}
module Mod {
  import A = Helpers
  method m() {
    assert A.addOne(5) == 6;
  }
}
```

```
module Helpers {
  ...
}
module Mod {
  import A = Helpers
  method m() {
    assert A.addOne(5) == 6;
  }
}
```

Note that inside `m()`, we have to use `A` instead of `Helpers`, as we bound it to a different name.
The name `Helpers` is not available inside `m()`, as only names that have been bound inside `Mod` are available.
In order to use the members from another module, it either has to be declared there with `module` or imported with `import`.

We don't have to give `Helpers` a new name, though, if we don't want to. We can write `import Helpers = Helpers` if we want to,
and Dafny even provides the shorthand `import Helpers` for this behavior. You can't bind two modules with the same name at the
same time, so sometimes you have to use the `=` version to ensure the names do not clash.

### Export sets

By default, an `import` will give access to all declarations (and their definitions) from the imported module. To control this more precisely we can instead use `export` sets. Each `export` set may have a list of declarations from the current module, given as `provides` or `reveals`. An `export` without a name is considered the default export for that module, and is used when no set is explicitly named.

```
module Helpers {
  export Spec provides addOne, addOne_result
  export Body reveals addOne
  export extends Spec
  function method addOne(n: nat): nat
  {
    n + 1
  }
  lemma addOne_result(n : nat)
     ensures addOne(n) == n + 1
  { }
}
```

In this example we declare 3 export sets, the `Spec` set grants access to the `addOne` function, but since it is declared with `provides` it does not give access to its definition. The `Body` export set declares `addOne` as `reveals`, which now gives access to the body of `addOne`. Finally, the default export is given as an `extends` of `Spec`, indicating that it simply gives all the declared exports that `Spec` does.

We can now choose any of these export sets when importing `Helpers` and get different views of it.

``` {.editonly}
module Helpers {
  export Spec provides addOne, addOne_result
  export Body reveals addOne
  export extends Spec
  function method addOne(n: nat): nat
  {
    n + 1
  }
  lemma addOne_result(n: nat)
     ensures addOne(n) == n + 1
  { }
}
```

```
module Mod1 {
  import A = Helpers`Body
  method m() {
    assert A.addOne(5) == 6; // succeeds, we have access to addOne's body
  }
  method m2() {
    //A.addOne_result(5); // error, addOne_result is not exported from Body
    assert A.addOne(5) == 6;
  }
}
module Mod2 {
  import A = Helpers`Spec
  method m() {
    assert A.addOne(5) == 6; // fails, we don't have addOne's body
  }
  method m2() {
    A.addOne_result(5);
    assert A.addOne(5) == 6; // succeeds due to result from addOne_result
  }
}
module Mod3 {
  import A = Helpers
  method m() {
    assert A.addOne(5) == 6; // fails, we don't have addOne's body
  }
}
```

We may also use `export` sets to control which type definitions are available. All type declarations (i.e. `newtype`, `type`, `datatype`, etc.) can be exported as `provides` or `reveals`. In the former case, modules which `import` that type will treat it as an opaque type.

```
module Helpers {
  export provides f, T
  export Body reveals f, T
  type T = int
  function f(): T { 0 }
}
module Mod {
  import A = Helpers
  function g(): A.T { 0 } // error, T is not known to be int, or even numeric
  function h(): A.T { A.f() } // okay
}
```

Once an `export` has been imported that `reveals` a previously opaque type, all existing uses of it are known to be the inner type.

``` {.editonly}
module Helpers {
  export provides f, T
  export Body reveals f, T
  type T = int
  function f(): T { 0 }
}
module Mod {
  import A = Helpers
  function h(): A.T { A.f() }
}
```

```
module Mod2 {
  import M = Mod
  import A = Helpers`Body
  function j(): int
    ensures j() == 0 //succeeds
  { M.h() }
}
```

As a convenient shorthand, the special identifier "*" can be given after `provides` or `reveals` to indicate that all declarations should be either provided or revealed.

```
module A {
   export All reveals * // reveals T, f, g
   export Spec provides * // provides T, f, g
   export Some provides * reveals g // provides T, f reveals g
   type T = int
   function f(): T { 0 }
   function g(): int { 2 }
}
```

We can also provide multiple exports at once to create an aggregate `import`.

```
module A {
  export Justf reveals f
  export JustT reveals T
  type T = int
  function f(): int { 0 }
}
module B {
  import A`{Justf,JustT}
  function g(): A.T { A.f() }
}
```

### Export Consistency


An `export` set must always present a coherent view of a module: anything that appears in an exported declaration must itself be exported. Revisiting the previous example, we could not create an `export` set that `reveals` `f` without also revealing `T`. This is for the simple reason that we would create a type constraint `0 : T` which cannot be solved if `T` is opaque. Similarly we cannot create an export set that `provides` or `reveals` `f` if we do not also at least provide `T`.

```
module Helpers {
  export provides f, T // good
  export Body reveals f, T // good
  export BadSpec reveals f, provides T // bad
  export BadSpec2 provides f // bad
  type T = int
  function f(): T { 0 }
}
```

Since we may define modules which contain both `import` and `export` declarations, we may need to export declarations from foreign modules in order to create a consistent `export` set. Declarations from foreign modules cannot be included in an `export` directly, however the `import` that provided them can.

``` {.editonly}
module Helpers {
  export provides f, T
  type T = int
  function f(): T { 0 }
}
```

```
module Mod {
  export Try1 reveals h // error
  export Try2 reveals h, provides A.f, A.T // error, can't provide these directly
  export reveals h, provides A // good
  import A = Helpers
  function h(): A.T { A.f() }
}
```

When importing `Mod` we now also gain qualified access to what is provided in its `import A`. We may also choose to directly import these, to give them a shorter name.

``` {.editonly}
module Helpers {
  export provides f, T
  type T = int
  function f(): T { 0 }
}
module Mod {
  export reveals h, provides A
  import A = Helpers
  function h(): A.T { A.f() }
}
```

```
module Mod2 {
  import M = Mod
  import MA = M.A
  function j(): M.A.T { M.h() }
  function k(): MA.T { j() }
}
```




## Opening Modules

 Sometimes prefixing the members of the module you imported with the name is tedious and ugly, even if you select a short name when importing it.
In this case, you can import the module as "`opened`", which causes all of its members to be available without adding the module name. The
`opened` keyword must immediately follow `import`, if it is present. For
example, we could write the previous `addOne` example as:

``` {.editonly}
module Helpers {
  function method addOne(n: nat): nat
  {
    n + 1
  }
}
module Mod {
  import opened Helpers
  method m() {
    assert addOne(5) == 6;
  }
}
```

```
module Mod {
  import opened Helpers
  method m() {
    assert addOne(5) == 6;
  }
}
```

When opening modules, the newly bound members will have low priority, so they will be hidden by local
definitions. This means if you define a local function called `addOne`, the function from `Helpers`
will no longer be available under that name. When modules are opened, the original name binding is still
present however, so you can always use the name that was bound to get to anything that is hidden.

``` {.editonly}
module Helpers {
  function method addOne(n: nat): nat
  {
    n + 1
  }
}
module Mod {
  import opened Helpers
  function addOne(n: nat): nat {
    n + 2
  }
  method m() {
    assert addOne(5) == 6; // this is now false,
                           // as this is the function just defined
    assert Helpers.addOne(5) == 6; // this is still true
  }
}
```

```
module Mod {
  import opened Helpers
  function addOne(n: nat): nat {
    n + 2
  }
  method m() {
    assert addOne(5) == 6; // this is now false,
                           // as this is the function just defined
    assert Helpers.addOne(5) == 6; // this is still true
  }
}
```

If you open two modules that both declare members with the same name, then neither member can
be referred to without a module prefix, as it would be ambiguous which one was meant. Just opening
the two modules is not an error, however, as long as you don't attempt to use members with common names.
The `opened` keyword can be used with any kind of `import` declaration, including the *module abstraction* form.


## Module Abstraction {#sec-module-abstraction}

Sometimes, using a specific implementation is unnecessary; instead, all that is needed is a module that implements some interface.
In that case, you can use an *abstract* module import. In Dafny, this is written `import A : B`. This means bind the name
`A` as before, but instead of getting the exact module `B`, you get any module which is a *refinement* of `B`. Typically, the module
`B` may have abstract type definitions, classes with bodyless methods, or otherwise be unsuitable to use directly. Because of the way refinement
is defined, any refinement of `B` can be used safely. For example, if we start with:

``` {.edit}
abstract module Interface {
  function method addSome(n: nat): nat
    ensures addSome(n) > n
}
abstract module Mod {
  import A : Interface
  method m() {
    assert 6 <= A.addSome(5);
  }
}
```

then we can be more precise if we know that `addSome` actually adds exactly one. The following module has this behavior. Further, the postcondition is stronger,
so this is actually a refinement of the `Interface` module.

``` {.edit}
module Implementation refines Interface {
  function method addSome(n: nat): nat
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}
```

We can then substitute `Implementation` for `A` in a new module, by declaring a refinement of `Mod` which defines `A` to be `Implementation`.

``` {.editonly}
abstract module Interface {
  function method addSome(n: nat): nat
    ensures addSome(n) > n
}
abstract module Mod {
  import A : Interface
  method m() {
    assert 6 <= A.addSome(5);
  }
}
module Implementation refines Interface {
  function method addSome(n: nat): nat
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}
module Mod2 refines Mod {
  import A = Implementation
  method m() {
    ...;
    // this is now provable, because we know A is Implementation
    assert 6 == A.addSome(5);
  }
}
```

When you refine an abstract import into a concrete one, the concrete module must be an explicit refinement of the abstract one (i.e. declared with `refines`).


## Module Ordering and Dependencies


  Dafny isn't particular about which order the modules appear in, but they must follow some rules to be well formed. As a rule of thumb, there should be a way to order the modules in a program
  such that each only refers to things defined <strong>before</strong> it in the source text. That doesn't mean the modules have to be given in that order. Dafny will figure out that order for you, assuming
  you haven't made any circular references. For example, this is pretty clearly meaningless:

``` {.edit}
import A = B
import B = A
```

You can have import statements at the toplevel, and you can import modules defined at the same level:

``` {.editonly}
import A = B
method m() {
  A.whatever();
}
module B {
  method whatever() {}
}
```

```
import A = B
method m() {
  A.whatever();
}
module B { ... }
```

In this case, everything is well defined because we can put `B` first, followed by the `A` import, and then finally `m()`. If there is no ordering,
then Dafny will give an error, complaining about a cyclic dependency.

Note that when rearranging modules and imports, they have to be kept in the same containing module, which disallows some pathological module structures. Also, the
imports and submodules are always considered to be first, even at the toplevel. This means that the following is not well formed:

``` {.edit}
method doIt() { }
module M {
  method m() {
    doIt();
  }
}
```

because the module `M` must come before any other kind of members, such as methods. To define global functions like this, you can put them in a module (called `Globals`, say)
and open it into any module that needs its functionality.
Finally, if you import via a path, such as `import A = B.C`, then this creates a dependency of `A` on `B`, as we need to know what B is (is it abstract or concrete, or a refinement?).



## Name Resolution

(Todo: The following has changed in Dafny. The description here should
be changed to reflect the new rules.)

When Dafny sees something like `A.B.C`, how does it know what each part refers to? The process Dafny uses to determine what identifier sequences like this refer
to is name resolution. Though the rules may seem complex, usually they do what you would expect. Dafny first looks up the initial identifier. Depending on what the first
identifier refers to, the rest of the identifier is looked up in the appropriate context. The full rules are as follows:

* Local variables, parameters and bound variables. These are things like `x`, `y`, and `i` in `var x;`, `... returns (y: int)`, and `forall i :: ...`.
* Classes, datatypes, and module names (provided this is not the only part of the identifier). Classes allow their static members to be accessed in this way,
    and datatypes allow their constructors to be accessed. Modules allow any of their members to be referred to like this
* Constructor names (if unambiguous). Any datatypes that don't need qualification (so the datatype name itself doesn't
    need a prefix), and also have a uniquely named constructor, can be referred to just by its name. So if `datatype List = Cons(List) | Nil`
    is the only datatype that declares `Cons` and `Nil` constructors, then you can write `Cons(Cons(Nil))`.
    If the constructor name is not unique, then you need to prefix it with the name of the datatype (for example `List.Cons(List.Nil))`).
    This is done per constructor, not per datatype.
* Fields, functions, and methods of the current class (if in a static context, then only static methods and functions are allowed).
    You can refer to fields of the current class either as `this.f` or `f`,
    assuming of course that `f` hasn't be hidden by one of the above. You can always prefix `this` if needed, which cannot be hidden. (Note, a field whose name is a string of digits must always have some prefix.)
* Static functions and methods in the enclosing module. Note, this refers only to functions and methods declared at the
  module level, not static members of a named class.

Opened modules are treated at each level, after the declarations in the current module. Opened modules only affect steps 2, 3 and 5.
If a ambiguous name is found, an error is generated, rather than continuing down the list.
After the first identifer, the rules are basically the same, except in the new context. For example, if the first identifier is a
module, then the next identifier looks into that module. Opened modules only apply within the module it is opened into. When looking
up into another module, only things explicitly declared in that module are considered.

