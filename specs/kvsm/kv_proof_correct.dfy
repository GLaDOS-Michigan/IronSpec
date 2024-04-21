//#title Sharded KV Store with Synchronous Communication
//#desc Build a refinement from a protocol (distributed sharded state) to
//#desc a specification (a logically-centralized abstract map).

// "Synchronous" means network messages are delivered instantaneously -- we
// keep the challenge simpler here by pretending messages can be sent and
// delivered atomically.

include "UtilitiesLibrary.dfy"
include "kvSmSpecIncorrect.dfy"




module ShardedKVProtocol {
  import opened UtilitiesLibrary
  import opened Types




  datatype Variables = Variables(maps:seq<map<Key, Value>>)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && |maps| == c.mapCount
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall idx:HostIdx | c.ValidHost(idx) :: v.maps[idx] == if idx==0 then InitialMap() else map[])
  }

  predicate Insert(c: Constants, v: Variables, v': Variables, idx: HostIdx, key: Key, value: Value)
  {
    && v.WF(c)
    && c.ValidHost(idx)
    && key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    //&& key in AllKeys() // implied by previous conjunct + Inv()ariant
    && v'.maps == v.maps[idx := v.maps[idx][key := value]]
  }

  predicate Query(c: Constants, v: Variables, v': Variables, idx: HostIdx, key: Key, output: Value)
  {
    && v.WF(c)
    && c.ValidHost(idx)
    && key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    && output == v.maps[idx][key]
    && v' == v  // UNCHANGED
  }

  // A possible enhancement exercise: transfer many key,value pairs in one step
  predicate Transfer(c: Constants, v: Variables, v': Variables, sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(sendIdx)
    && c.ValidHost(recvIdx)
    && key in v.maps[sendIdx]
    && v.maps[sendIdx][key] == value
    && v'.maps[sendIdx] == MapRemoveOne(v.maps[sendIdx], key)  // key leaves sending map
    && v'.maps[recvIdx] == v.maps[recvIdx][key := value]    // key appears in recv map
    && (forall otherIdx:HostIdx | c.ValidHost(otherIdx) && otherIdx != sendIdx && otherIdx != recvIdx
        :: v'.maps[otherIdx] == v.maps[otherIdx]) // unchanged other participants
  }

  datatype Step =
    | InsertStep(idx: HostIdx, key: Key, value: Value)
    | QueryStep(idx: HostIdx, key: Key, output: Value)
    | TransferStep(sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    match step
      case InsertStep(idx, key, value) => Insert(c, v, v', idx, key, value)
      case QueryStep(idx, key, output) => Query(c, v, v', idx, key, output)
      case TransferStep(sendIdx, recvIdx, key, value) => Transfer(c, v, v', sendIdx, recvIdx, key, value)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}

module RefinementProof {
  import opened UtilitiesLibrary
  import opened Types
  import opened ShardedKVProtocol
  import opened MapSpec


  predicate HostHasKey(c: Constants, v: ShardedKVProtocol.Variables, hostidx:HostIdx, key:Key)
    requires v.WF(c)
  {
    && c.ValidHost(hostidx)
    && key in v.maps[hostidx]
  }


  function KeyHolder(c: Constants, v: ShardedKVProtocol.Variables, key:Key) : HostIdx
    requires v.WF(c)
    requires exists hostidx :: HostHasKey(c, v, hostidx, key);
  {
    var hostidx:HostIdx :| HostHasKey(c, v, hostidx, key);
    hostidx
  }


  function AbstractionOneKey(c: Constants, v: ShardedKVProtocol.Variables, key:Key) : Value
    requires v.WF(c)
  {
    if (exists hostidx :: HostHasKey(c, v, hostidx, key)) then v.maps[KeyHolder(c, v, key)][key] else DefaultValue()
  }

  function MapDomains(c: Constants, v: ShardedKVProtocol.Variables) : seq<set<Key>>
    requires v.WF(c)
  {
    seq(c.mapCount, i requires 0<=i<c.mapCount => v.maps[i].Keys)
  }

  function KnownKeys(c: Constants, v: ShardedKVProtocol.Variables) : set<Key>
    requires v.WF(c)
  {
    UnionSeqOfSets(MapDomains(c, v))
  }


  lemma HostKeysSubsetOfKnownKeys(c: Constants, v: ShardedKVProtocol.Variables, count: nat)
    requires v.WF(c)
    requires count <= c.mapCount
    ensures forall idx | 0 <= idx < count :: v.maps[idx].Keys <= KnownKeys(c, v)
  {
    forall idx | 0 <= idx < count ensures v.maps[idx].Keys <= KnownKeys(c, v)
    {
      SetsAreSubsetsOfUnion(MapDomains(c, v));
      assert v.maps[idx].Keys == MapDomains(c, v)[idx];  // trigger
    }
  }

  function Abstraction(c: Constants, v: ShardedKVProtocol.Variables) : MapSpec.Variables
    requires v.WF(c)
  {

    MapSpec.Variables(map key | key in KnownKeys(c, v) :: AbstractionOneKey(c, v, key))

  }

  predicate {:opaque} KeysHeldUniquely(c: Constants, v: ShardedKVProtocol.Variables)
    requires v.WF(c)
  {
    forall key, hostidx:HostIdx, otherhost:HostIdx
        | && c.ValidHost(hostidx) && c.ValidHost(otherhost)
          && key in v.maps[hostidx] && key in v.maps[otherhost]
        :: hostidx == otherhost
  }

  predicate Inv(c: Constants, v: ShardedKVProtocol.Variables)
  {
    && v.WF(c)
    && KnownKeys(c, v) == AllKeys()
    && KeysHeldUniquely(c, v)

  }


  lemma KnownKeysSubsetOfHostKeys(c: Constants, v: ShardedKVProtocol.Variables)
    requires v.WF(c)
    ensures forall key | key in KnownKeys(c, v) :: (exists hostidx :: HostHasKey(c, v, hostidx, key))
  {
    EachUnionMemberBelongsToASet(MapDomains(c, v));
    forall key | key in KnownKeys(c, v)
      ensures (exists hostidx :: HostHasKey(c, v, hostidx, key))
    {
      var idx :| 0 <= idx < |MapDomains(c, v)| && key in MapDomains(c, v)[idx];
      assert HostHasKey(c, v, idx, key);
    }
  }


  lemma RefinementInit(c: Constants, v: ShardedKVProtocol.Variables)
    requires c.WF()
    requires ShardedKVProtocol.Init(c, v)
    ensures MapSpec.Init(Abstraction(c, v))
    ensures Inv(c, v)
  {

    assert MapDomains(c, v)[0] == AllKeys();

    HostKeysSubsetOfKnownKeys(c, v, c.mapCount);
    KnownKeysSubsetOfHostKeys(c, v);

    reveal_KeysHeldUniquely();

  }

  lemma AnyHostWithKeyIsKeyHolder(c: Constants, v: ShardedKVProtocol.Variables, hostidx:HostIdx, key:Key)
    requires v.WF(c)
    requires KeysHeldUniquely(c, v)
    requires HostHasKey(c, v, hostidx, key)
    ensures KeyHolder(c, v, key) == hostidx
  {
    reveal_KeysHeldUniquely();
  }


  lemma InsertPreservesInvAndRefines(c: Constants, v: ShardedKVProtocol.Variables, v': ShardedKVProtocol.Variables, insertHost: HostIdx, insertedKey: Key, value: Value)
    requires Inv(c, v)
    requires ShardedKVProtocol.Next(c, v, v')
    requires c.ValidHost(insertHost)
    requires Insert(c, v, v', insertHost, insertedKey, value)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {

    assert v.maps[insertHost].Keys == v'.maps[insertHost].Keys;
    assert MapDomains(c, v) == MapDomains(c, v');
    assert KnownKeys(c, v') == KnownKeys(c, v);

    reveal_KeysHeldUniquely();


    forall key | key in AllKeys() && key != insertedKey 
      ensures AbstractionOneKey(c, v, key) == AbstractionOneKey(c, v', key)
    {
      KnownKeysSubsetOfHostKeys(c, v);
      KnownKeysSubsetOfHostKeys(c, v');

      assert v'.maps[KeyHolder(c, v', key)][key] == v.maps[KeyHolder(c, v, key)][key];
    }

    assert HostHasKey(c, v', insertHost, insertedKey);
    assert v'.maps[insertHost][insertedKey] == value;
    HostKeysSubsetOfKnownKeys(c, v', insertHost + 1);

    assert Abstraction(c, v').mapp == Abstraction(c, v).mapp[insertedKey := value];
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.InsertOpStep(insertedKey, value));
  }

  lemma QueryPreservesInvAndRefines(c: Constants, v: ShardedKVProtocol.Variables, v': ShardedKVProtocol.Variables, queryHost: HostIdx, key: Key, output: Value)
    requires Inv(c, v)
    requires ShardedKVProtocol.Next(c, v, v')
    requires c.ValidHost(queryHost)
    requires Query(c, v, v', queryHost, key, output)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
    assert Abstraction(c, v) == Abstraction(c, v');
    HostKeysSubsetOfKnownKeys(c, v, queryHost + 1);
    assert key in AllKeys();
    AnyHostWithKeyIsKeyHolder(c, v, queryHost, key);
    assert AbstractionOneKey(c, v, key) == output;
    assert output == Abstraction(c, v).mapp[key];

    assert MapSpec.QueryOp(Abstraction(c, v), Abstraction(c, v'), key, output);
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.QueryOpStep(key, output));

  }

  lemma TransferPreservesInvAndRefines(c: Constants, v: ShardedKVProtocol.Variables, v': ShardedKVProtocol.Variables, sendIdx: HostIdx, recvIdx: HostIdx, sentKey: Key, value: Value)
    requires Inv(c, v)
    requires ShardedKVProtocol.Next(c, v, v')
    requires c.ValidHost(sendIdx)
    requires c.ValidHost(recvIdx)
    requires Transfer(c, v, v', sendIdx, recvIdx, sentKey, value)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
    reveal_KeysHeldUniquely();

    forall key:Key | key in AllKeys()
      ensures AbstractionOneKey(c, v, key) == AbstractionOneKey(c, v', key)
      ensures key in KnownKeys(c, v')
    {
      if key == sentKey {
        assert HostHasKey(c, v, sendIdx, key);
        assert HostHasKey(c, v', recvIdx, key);
      } else {
        KnownKeysSubsetOfHostKeys(c, v);
        var hostidx:HostIdx :| HostHasKey(c, v, hostidx, key);
        assert HostHasKey(c, v', hostidx, key);
      }
      HostKeysSubsetOfKnownKeys(c, v', c.mapCount);
    }

    forall key | key in KnownKeys(c, v')
      ensures key in AllKeys()
    {
      if (key == sentKey) {
        assert key in v.maps[sendIdx];
      } else {
        KnownKeysSubsetOfHostKeys(c, v');
        var hostidx:HostIdx :| HostHasKey(c, v', hostidx, key);
        assert key in v.maps[hostidx];
      }
      HostKeysSubsetOfKnownKeys(c, v, c.mapCount);
    }

    assert Abstraction(c, v) == Abstraction(c, v');
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.NoOpStep());

  }

  lemma RefinementNext(c: Constants, v: ShardedKVProtocol.Variables, v': ShardedKVProtocol.Variables)
    requires Inv(c, v)
    requires ShardedKVProtocol.Next(c, v, v')
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
    var step :| ShardedKVProtocol.NextStep(c, v, v', step);
    match step
      case InsertStep(idx, key, value) => {
        InsertPreservesInvAndRefines(c, v, v', idx, key, value);
      }
      case QueryStep(idx, key, output) => {
        QueryPreservesInvAndRefines(c, v, v', idx, key, output);
      }
      case TransferStep(sendIdx, recvIdx, key, value) => {
        TransferPreservesInvAndRefines(c, v, v', sendIdx, recvIdx, key, value);
      }
  }
}