module Types {
  // Rather than concretely explain the Key and Value types, we define the spec
  // and protocol over some uninterpreted types. The type declaration below says "there
  // is some type Key, but this protocol's behavior doesn't depend on what actual
  // type it is."

  // We need to tell Dafny two things about the type to convince it the type behaves
  // mathematically:
  // (==) means whatever this type is, it has equality defined on it.
  // !new means this type can't be allocated on the heap; it's a mathematical
  // immutable object.
  // Since we're in math-land, not implementation-land, we always want both features
  // of all types, so we declare them on these otherwise-unspecified types.
  // Missing == gives "map domain type must support equality" errors.
  // Missing !new gives "...not allowed to depend on the set of allocated
  // references" errors.
  type Key(==, !new)

  // Dafny's map<> type requires a finite domain. It also has an imap<> type that
  // allows an infinite domain, but we'd like to defer that complexity, so we'll stick
  // with finite maps.
  // Looking forward to the implementation, we can start with no keys stored, but we
  // are going to need to store "shard authority" information (which host is responsible
  // for each key) for every possible key, so eventually we're going to need to
  // have maps that contain every possible key. If we want to avoid imap<> for now,
  // then we'll need a finite keyspace. `type Key` is uninterpreted, and there's
  // no easy way to declare that it's finite.
  // (Side note: actually there is; Dafny has a predicate type constructor, but it's
  // flaky and sometimes crashes Dafny, so we're going to steer clear of it, too.)

  // So, just as we assume there's some space of Keys, let's assume a function that
  // defines a finite subset of those keys as the keyspace we're actually going to use.
  // We leave the function body absent, which means it's an axiom: we don't provide
  // the function, but assume such a function exists.
  // Everywhere we use a Key, we'll also require it to be in AllKeys().
  function AllKeys() : set<Key> // !!!: way to declare a const variable with type set<key> without specifying it

  type Value(==, !new)

  // To keep the API simple, we omit the concept of "the absence of a key", and instead
  // define a DefaultValue that keys have until Inserted otherwise.
  function DefaultValue() : Value
    // Again, No body -> this is an axiom.

  // This map comprehension assigns the DefaultValue to every key in the finite AllKeys()
  // keyspace. (Note that here the finite-ness of AllKeys() is now essential, as
  // it shows Dafny than the map has finite domain.)
  function InitialMap() : map<Key, Value>
  {
    map key | key in AllKeys() :: DefaultValue()
  }

  type HostIdx = nat

  datatype Constants = Constants(mapCount: nat)
  {
    predicate WF() { 0 < mapCount }
    predicate ValidHost(idx: HostIdx) { idx < mapCount }
  }
}
// This module defines a Map state machine that serves as the system specification.
// You can tell by looking at this state machine that Key-Value pairs that get inserted
// are returned in Queries until otherwise inserted. It only talks about the semantics
// of Insert and Query; all of the details of a sharded implementation are left to
// the implementation.
module MapSpec {
  import opened Types

  datatype Variables = Variables(mapp:map<Key, Value>)

  predicate Init(v: Variables)
  {
    v.mapp == InitialMap()
    // Initially, every key maps to DefaultValue.
  }

  predicate InsertOp(v:Variables, v':Variables, key:Key, value:Value)
  {
    // A well-formed condition: we're not even gonna talk about keys other than AllKeys().
    && key in AllKeys()
    // Replace key with value. v.mapp domain remains AllKeys().
    && v'.mapp == v.mapp[key := value]
  }

  predicate QueryOp(v:Variables, v':Variables, key:Key, output:Value)
  {
    && key in AllKeys()
    // This is always true, but only visible by an inductive proof. We assume
    // it here so we can dereference v.mapp[key] on the next line. (If my claim
    // were wrong, then some Querys would be rejected by this test, which is a
    // liveness failure but not a safety failure.)
    && key in v.mapp
    && output == DefaultValue()
    && v' == v  // no change to map state
  }

  datatype Step =
    | InsertOpStep(key:Key, value:Value)
    | QueryOpStep(key:Key, output:Value)
    | NoOpStep()

  predicate NextStep(v: Variables, v': Variables, step:Step)
  {
    match step
      case InsertOpStep(key, value) => InsertOp(v, v', key, value)
      case QueryOpStep(key, output) => QueryOp(v, v', key, output)
      case NoOpStep => v' == v // ???: difference
  }

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }
}