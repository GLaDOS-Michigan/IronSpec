# 22. Refinement {#sec-module-refinement}

Refinement is the process of replacing something somewhat abstract with something somewhat more concrete.
For example, in one module one might declare a type name, with no definition,
such as `type T`, and then in a refining module, provide a definition.
One could prove general properties about the contents of an (abstract) module,
and use that abstract module, and then later provide a more concrete implementation without having to redo all of the proofs.

Dafny supports _module refinement_, where one module is created from another,
and in that process the new module may be made more concrete than the previous.
More precisely, refinement takes the following form in Dafny. One module
declares some program entities. A second module _refines_ the first by
declaring how to augment or replace (some of) those program entities.
The first module is called the _refinement parent_; the second is the
_refining_ module; the result of combining the two (the original declarations
and the augmentation directives) is the _assembled_ module or _refinement result_.

Syntactically, the refinement parent is a normal module declaration.
The refining module declares which module is its refinement parent with the
`refines` clause:
```
module P { // refinement parent
}
module M refines P { // refining module
}
```

The refinement result is created as follows.

0) The refinement result is a module within the same enclosing module as the
refining module, has the same name, and in fact replaces the refining module  in their shared scope.

1) All the declarations (including import and export declarations) of the parent are copied into the refinement result.
These declarations are _not_ re-resolved. That is, the assignment of
declarations and types to syntactic names is not changed. The refinement
result may exist in a different enclosing module and with a different set of
imports than the refinement parent, so that if names were reresolved, the
result might be different (and possibly not semantically valid).
This is why Dafny does not re-resolve the names in their new context.

2) All the declarations of the refining module that have different names
than the declarations in the refinement parent are also copied into the
refinement result.
However, because the refining module is just a set of augmentation
directives and may refer to names copied from the refinement parent,
resolution of names and types of the declarations copied in this step is
performed in the context of the full refinement result.

3) Where declarations in the parent and refinement module have the same name,
the second refines the first and the combination, a refined declaration, is
the result placed in the refinement result module, to the exclusion of the
declarations with the same name from the parent and refinement modules.

The way the refinement result declarations are assembled depends on the kind of declaration;
the rules are described in subsections below.

So that it is clear that refinement is taking place, refining declarations
have some syntactic indicator that they are refining some parent declaration.
Typically this is the presence of a `...` token.

## 22.1. Export set declarations

A refining export set declaration begins with the syntax
````grammar
"export" Ident ellipsis
````
but otherwise contains the same `provides`, `reveals` and `extends` sections,
with the ellipsis indicating that it is a refining declaration.

The result declaration has the same name as the two input declarations and the unions of names from each of the `provides`, `reveals`, and `extends`
sections, respectively.

An unnamed export set declaration from the parent is copied into the result
module with the name of the parent module. The result module has a default
export set according to the general rules for export sets, after all of
the result module's export set declarations have been assembled.

## 22.2. Import declarations

Aliasing import declarations are not refined. The result module contains the union
of the import declarations from the two input modules.
There must be no names in common among them.

Abstract import declarations (declared with `:` instead of `=`, [Section 4.6](#sec-module-abstraction)) are refined. The refinement parent contains the
abstract import and the refining module contains a regular aliasing
import for the same name. Dafny checks that the refining import _adheres_ to
the abstract import.

## 22.3. Sub-module declarations

TODO

## 22.4. Const declarations

Const declarations can be refined as in the following example.

```
module A {
  const ToDefine: int
  const ToDefineWithoutType: int
  const ToGhost: int := 1
}

module B refines A {
  const ToDefine: int := 2
  const ToDefineWithoutType ... := 3
  ghost const ToGhost: int
  const NewConst: int
}
```

Formally, a child `const` declaration may refine a `const` declaration
from a parent module if

* the parent has no initialization,
* the child has the same type as the parent, and
* one or both of the following holds:
   * the child has an initializing expression
   * the child is declared `ghost` and the parent is not `ghost`.

A refining module can also introduce new `const` declarations that do
not exist in the refinement parent.

## 22.5. Method declarations

Method declarations can be refined as in the following example.

```
module A {
  method ToImplement(x: int) returns (r: int)
    ensures r > x

  method ToStrengthen(x: int) returns (r: int)

  method ToDeterminize(x: int) returns (r: int)
    ensures r >= x
  {
    var y :| y >= x;
    return y;
  }

  method ToSuperimpose(x: int) returns (r: int)
  {
    var y: int := x;
    if y < 0 {
      return -y;
    } else {
      return y;
    }
  }

}

module B refines A {
  method ToImplement(x: int) returns (r: int)
  {
    return x + 2;
  }

  method ToStrengthen...
    ensures r == x*2
  {
    return x*2;
  }

  method ToDeterminize(x: int) returns (r: int)
  {
    return x;
  }

  method ToSuperimpose(x: int) returns (r: int)
  {
    ...;
    if y < 0 {
      print "inverting";
    } else {
      print "not modifying";
    }
  }
}
```

Formally, a child `method` definition may refine a parent `method`
declaration or definition by performing one or more of the following
operations:

* provide a body missing in the parent (as in `ToDefine`),
* strengthen the postcondition of the parent method by adding one or more
  `ensures` clauses (as in `ToStrengthen`),
* provide a more deterministic version of a non-deterministic parent
  body (as in `ToDeterminize`), or
* superimpose the body of the parent method with additional statements
  (as in `ToSuperimpose`).

The type signature of a child method must be the same as that of the
parent method it refines. This can be ensured by providing an explicit
type signature equivalent to that of the parent (with renaming of
parameters allowed) or by using an ellipsis (`...`) to indicate copying
of the parent type signature. The body of a child method must satisfy
any ensures clauses from its parent in addition to any it adds.

To introduce additional statements, the child method can include
ellipses within the body to stand in for portions of code from the
parent body. Dafny then attempts to merge the body of the child with the
body of the parent by filling in the ellipses. In the `ToSuperimpose`
example, the explicit `...` at the beginning will expand to the variable
declaration for `y`. In addition, there is an implicit `...` before
every `}`, allowing new statements to be introduced at the beginning of
each block. In `ToSuperimpose`, these implicit ellipses expand to the
return statements in the parent method.

To help with understanding of the merging process, the IDE provides
hover text that shows what each `...` or `}` expands to.

The refinement result for `ToSuperimpose` will be as follows.

```
method ToSuperimpose(x: int) returns (r: int)
{
  var y: int := x;
  if y < 0 {
    print "inverting";
    return -y;
  } else {
    print "not modifying";
    return y;
  }
}
```

In general, a child method can add local variables and assignments,
add some forms of `assert`, convert an `assume ` to an `assert` (using
`assert ...;`), replace a non-deterministic operation with a more
deterministic one, and insert additional `return` statements. A child
method cannot otherwise change the control-flow structure of a method.
Full details of the algorithm used to perform the merge operation are
available in [this
paper](https://dl.acm.org/doi/10.1007/s00165-012-0254-3). See also [this
comment](https://github.com/dafny-lang/dafny/blob/76c8d599155f45e9745ce854ab54d0ab4be52049/Source/Dafny/RefinementTransformer.cs#L55)
in the source code.

A refined method is allowed only if it does not invalidate any parent
lemmas that mention it.

A refining module can also introduce new `method` declarations or
definitions that do not exist in the refinement parent.

## 22.6. Lemma declarations

As lemmas are (ghost) methods, the description of method refinement from
the previous section also applies to lemma refinement.

A valid refinement is one that does not invalidate any proofs. A lemma
from a refinement parent must still be valid for the refinement result
of any method or lemma it mentions.

## 22.7. Function and predicate declarations

Function (and equivalently predicate) declarations can be refined as in
the following example.

```
module A {
  function F(x: int): (r: int)
    ensures r > x

  function G(x: int): (r: int)
    ensures r > x
  { x + 1 }
}

module B refines A {
  function F...
  { x + 1 }

  function G...
    ensures r == x + 1
}
```

Formally, a child `function` (or `predicate`) definition can refine a
parent `function` (or `predicate`) declaration or definition to

* provide a body missing in the parent,
* strengthen the postcondition of the parent function by adding one or more
  `ensures` clauses.

The relation between the type signature of the parent and child function
is the same as for methods and lemmas, as described in the previous section.

A refining module can also introduce new `function` declarations or
definitions that do not exist in the refinement parent.

## 22.8. Iterator declarations

TODO

## 22.9. Class and trait declarations

TODO

## 22.10. Type declarations
-- opaque, type synonym, subset, newtype, datatype

TODO

