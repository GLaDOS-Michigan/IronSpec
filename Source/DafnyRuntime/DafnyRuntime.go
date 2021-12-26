// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

package dafny

import (
  "fmt"
  big "math/big"
  refl "reflect"
  "runtime"
)

/******************************************************************************
 * Generic values
 ******************************************************************************/

// An EqualsGeneric can be compared to any other object.  This method should
// *only* return true when the other value is of the same type.
type EqualsGeneric interface {
  EqualsGeneric(other interface{}) bool
}

// AreEqual compares two values for equality in a generic way.  Besides the
// refl.DeepEqual logic (to which this method defers as a last resort), the
// values are handled intelligently if their type is refl.Value or any type that
// implements the EqualsGeneric interface.
func AreEqual(x, y interface{}) bool {
  if IsDafnyNull(x) {
    return IsDafnyNull(y)
  }
  if IsDafnyNull(y) {
    return false
  }
  switch x := x.(type) {
  case refl.Value:
    {
      y, ok := y.(refl.Value)
      return ok && x.CanInterface() && y.CanInterface() &&
        AreEqual(x.Interface(), y.Interface())
    }
  case EqualsGeneric:
    return x.EqualsGeneric(y)
  default:
    return refl.DeepEqual(x, y)
  }
}

func IsDafnyNull(x interface{}) bool {
  if x == nil {
    return true
  }
  v := refl.ValueOf(x)
  if v.Kind() == refl.Ptr {
    return v.IsNil()
  }
  return false
}

func isNil(v refl.Value) bool {
  switch v.Kind() {
  case refl.Chan, refl.Func, refl.Map, refl.Ptr, refl.Slice:
    return v.IsNil()
  case refl.Interface:
    return v.IsNil() || v.Elem().IsNil()
  default:
    return false
  }
}

// String formats the given value using fmt.Sprint, unless it's nil, in which
// case it formats it as "null" to conform to other languages' output.
func String(x interface{}) string {
  if x == nil {
    return "null"
  }
  v := refl.ValueOf(x)
  if isNil(v) {
    return "null"
  }
  if v.Kind() == refl.Func {
    return v.Type().String()
  }
  return fmt.Sprint(x)
}

// Print prints the given value using fmt.Print, formatted using String.
func Print(x interface{}) {
  fmt.Print(String(x))
}

// SetFinalizer is a re-export of runtime.SetFinalizer.  Included here so that
// only this module needs to be imported by every Dafny module.
func SetFinalizer(x interface{}, f interface{}) {
  runtime.SetFinalizer(x, f)
}

/******************************************************************************
 * Run-time type descriptors (RTDs)
 ******************************************************************************/

// A TypeDescriptor has the ability to produce a default value for an associated type.
type TypeDescriptor interface {
  Default() interface{}
}

func CreateStandardTypeDescriptor(value interface{}) TypeDescriptor {
  return standardTypeDescriptor{value}
}

type standardTypeDescriptor struct {
  defaultValue interface{}
}

func (rtd standardTypeDescriptor) Default() interface{} {
  return rtd.defaultValue
}

// IntType is the RTD for int
var IntType = CreateStandardTypeDescriptor(Zero)

// BoolType is the RTD of bool
var BoolType = CreateStandardTypeDescriptor(false)

// CharType is the RTD of char
var CharType = CreateStandardTypeDescriptor(Char('D'))  // See CharType.DefaultValue in Dafny source code

// RealType is the RTD for real
var RealType = CreateStandardTypeDescriptor(ZeroReal)

// Int64Type is the RTD of int64.
var Int64Type = CreateStandardTypeDescriptor(int64(0))

// PossiblyNullType is the RTD of any possibly null reference type
var PossiblyNullType = CreateStandardTypeDescriptor((*interface{})(nil))

// Uint8Type is the RTD of uint8
var Uint8Type = CreateStandardTypeDescriptor(uint8(0))

// Uint16Type is the RTD of uint16
var Uint16Type = CreateStandardTypeDescriptor(uint16(0))

// Uint32Type is the RTD of uint32
var Uint32Type = CreateStandardTypeDescriptor(uint32(0))

// Uint64Type is the RTD of uint64
var Uint64Type = CreateStandardTypeDescriptor(uint64(0))

// SetType is the RTD for sets
var SetType = CreateStandardTypeDescriptor(EmptySet)

// MultiSetType is the RTD for multisets
var MultiSetType = CreateStandardTypeDescriptor(EmptyMultiSet)

// SeqType is the RTD for sequences
var SeqType = CreateStandardTypeDescriptor(EmptySeq)

// MapType is the RTD for maps
var MapType = CreateStandardTypeDescriptor(EmptyMap)

/******************************************************************************
 * Trait parent information
 ******************************************************************************/

// Every class gets compiled to have a ParentTraits_ method, which returns the
// list of Dafny parent traits (including transitive parent traits). This is
// used to determine, at run time, if a given object satisfies a particular trait.
// While it is unusual that this information is needed, it is needed in a situation
// like
//   var s: set<UberTrait> := ...
//   // the following line requires run-time check that t (of type UberTrait) is a Trait
//   var ts := set t: Trait | t in s;
// A more straightforward situation is the expression
//   x is Trait

type TraitID struct {
  dummy byte
}

type TraitOffspring interface {
  ParentTraits_() []*TraitID
}

func InstanceOfTrait(obj TraitOffspring, trait *TraitID) bool {
  for _, parent := range obj.ParentTraits_() {
    if parent == trait {
      return true
    }
  }
  return false
}

// Use this method to test if an object "p" has a given class type (denoted by the
// type of "q"). More generally, this method returns true if p and q are of the
// same type. It is assumed that neither "p" nor "q" denotes a Dafny "null" value.

func InstanceOf(p interface{}, q interface{}) bool {
  return refl.TypeOf(p) == refl.TypeOf(q)
}

/******************************************************************************
 * Object
 ******************************************************************************/

type Object struct {
  dummy byte
}

func New_Object() *Object {
  _this := Object{}
  return &_this
}

func (_this *Object) Equals(other *Object) bool {
  return _this == other
}

func (_this *Object) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*Object)
  return ok && _this.Equals(other)
}

func (*Object) String() string {
  return "object"
}

func (_this *Object) ParentTraits_() []*TraitID {
  return [](*TraitID){};
}
var _ TraitOffspring = &Object{}

/******************************************************************************
 * Characters
 ******************************************************************************/

// A Char is a rune in a wrapper so that we can detect it and treat it
// distinctly from int32.
type Char rune

func (char Char) String() string {
  return fmt.Sprintf("%c", rune(char))
}

// AllChars returns an iterator that returns all 16-bit characters.
func AllChars() Iterator {
  c := int32(0)
  return func() (interface{}, bool) {
    if c >= 0x10000 {
      return -1, false
    } else {
      ans := Char(c)
      c++
      return ans, true
    }
  }
}

/******************************************************************************
 * Slices
 ******************************************************************************/

func sliceEquals(s1, s2 []interface{}) bool {
  return len(s1) == len(s2) && sliceIsPrefixAfterLengthCheck(s1, s2)
}

func sliceIsPrefixOf(s1, s2 []interface{}) bool {
  return len(s1) <= len(s2) && sliceIsPrefixAfterLengthCheck(s1, s2)
}

func sliceIsProperPrefixOf(s1, s2 []interface{}) bool {
  return len(s1) < len(s2) && sliceIsPrefixAfterLengthCheck(s1, s2)
}

func sliceIsPrefixAfterLengthCheck(s1, s2 []interface{}) bool {
  for i, v := range s1 {
    if !(AreEqual(v, s2[i])) {
      return false
    }
  }
  return true
}

func sliceContains(s []interface{}, value interface{}) bool {
  for _, v := range s {
    if AreEqual(v, value) {
      return true
    }
  }
  return false
}

// Iterator returns an iterator over the sequence.
func sliceIterator(s []interface{}) Iterator {
  i := 0
  n := len(s)
  return func() (interface{}, bool) {
    if i >= n {
      return nil, false
    }
    ans := s[i]
    i++
    return ans, true
  }
}

func stringOfElements(s []interface{}) string {
  str := ""
  for i, v := range s {
    if i > 0 {
      str += ", "
    }
    str += String(v)
  }
  return str
}

/******************************************************************************
 * Iteration
 ******************************************************************************/

// An Iterator is a function that can be called multiple times to get successive
// values, until the second value returned is false.
type Iterator = func() (interface{}, bool)

// An Iterable can produce an iterator, which we represent as a function which
// can be called to get successive values.
type Iterable interface {
  Iterator() Iterator
}

// Iterate gets an iterator from a value that is either an iterator or an
// iterable.
func Iterate(over interface{}) Iterator {
  switch over := over.(type) {
  case Iterator:
    return over
  case Iterable:
    return over.Iterator()
  default:
    if refl.TypeOf(over).Kind() != refl.Slice {
      panic(fmt.Errorf("Not iterable: %v", over))
    } else {
      return anySliceIterator(over)
    }
  }
}

func anySliceIterator(slice interface{}) Iterator {
  val := refl.ValueOf(slice)
  n := val.Len()
  i := 0
  return func() (interface{}, bool) {
    if i >= n {
      return nil, false
    } else {
      ans := val.Index(i).Interface()
      i++
      return ans, true
    }
  }
}

// Quantifier calculates whether a predicate holds either for all values yielded
// by an iterator or for at least one.
func Quantifier(iter interface{}, isForAll bool, pred interface{}) bool {
  predVal := refl.ValueOf(pred)

  for i := Iterate(iter); ; {
    v, ok := i()
    if !ok {
      return isForAll
    }
    if predVal.Call([]refl.Value{refl.ValueOf(v)})[0].Interface() != isForAll {
      return !isForAll
    }
  }
}

// SingleValue produces an iterator that yields only a single value.
func SingleValue(value interface{}) Iterator {
  done := false
  return func() (interface{}, bool) {
    if done {
      return nil, false
    } else {
      done = true
      return value, true
    }
  }
}

// AllBooleans returns an iterator that returns false, then returns true.
func AllBooleans() Iterator {
  phase := 0
  return func() (interface{}, bool) {
    switch phase {
    case 0:
      phase = 1
      return false, true
    case 1:
      phase = 2
      return true, true
    default:
      return false, false
    }
  }
}

/******************************************************************************
 * Sequences
 ******************************************************************************/

// A Seq is a Go slice representing a one-dimensional array.  There aren't any
// methods for updating; instead, you can update by mutating the value returned
// by Index (either by using its Set method or by getting a pointer using its
// Addr method).
type Seq struct {
  contents []interface{}
  isString bool
}

// EmptySeq is the empty sequence.
var EmptySeq = SeqOf()

// Create a sequence from a length and an element initializer
func SeqCreate(n Int, init func (Int) interface{}) Seq {
  len := n.Int()
  arr := make([]interface{}, len)
  for i := 0; i < len; i++ {
    arr[i] = init(IntOf(i))
  }
  return Seq{arr, false}
}

// SeqOf returns a sequence containing the given values.
func SeqOf(values ...interface{}) Seq {
  // Making a defensive copy here because variadic functions can get hinky
  // if someone says SeqOf(slice...) and then mutates slice.
  arr := make([]interface{}, len(values))
  copy(arr, values)
  return Seq{arr, false}
}

// SeqOfChars returns a sequence containing the given character values.
func SeqOfChars(values ...Char) Seq {
  arr := make([]interface{}, len(values))
  for i, v := range values {
    arr[i] = v
  }
  return Seq{arr, true}
}

// SeqOfString converts the given string into a sequence of characters.
func SeqOfString(str string) Seq {
  // Need to make sure the elements of the array are Chars
  arr := make([]interface{}, len(str))
  for i, v := range str {
    arr[i] = Char(v)
  }
  return Seq{arr, true}
}

func (seq Seq) SetString() Seq {
        return Seq{seq.contents, true}
}

// Index finds the sequence element at the given index.
func (seq Seq) Index(i Int) interface{} {
  return seq.IndexInt(i.Int())
}

// IndexInt finds the sequence element at the given index.
func (seq Seq) IndexInt(i int) interface{} {
  return seq.contents[i]
}

// Update returns a new sequence with the given index set to the given value.
func (seq Seq) Update(i Int, v interface{}) Seq {
  return seq.UpdateInt(i.Int(), v)
}

// UpdateInt returns a new sequence with the given index set to the given value.
func (seq Seq) UpdateInt(i int, v interface{}) Seq {
  arr := make([]interface{}, len(seq.contents))
  copy(arr, seq.contents[:i])
  arr[i] = v
  copy(arr[i+1:], seq.contents[i+1:])
  return Seq{arr, seq.isString}
}

// Len finds the length of the sequence.
func (seq Seq) Len() Int {
  return IntOf(seq.LenInt())
}

// LenInt finds the length of the sequence as an int.
func (seq Seq) LenInt() int {
  return len(seq.contents)
}

// Cardinality finds the length of the sequence.
func (seq Seq) Cardinality() Int {
  return seq.Len()
}

// CardinalityInt finds the length of the sequence as an int.
func (seq Seq) CardinalityInt() int {
  return seq.LenInt()
}

// Contains finds whether the value is equal to any element in the sequence.
func (seq Seq) Contains(value interface{}) bool {
  return sliceContains(seq.contents, value)
}

// Iterator returns an iterator over the sequence.
func (seq Seq) Iterator() Iterator {
  return sliceIterator(seq.contents)
}

// Subseq gets the selected portion of the sequence as a new sequence.
func (seq Seq) Subseq(lo, hi Int) Seq {
  var slice []interface{}
  if !lo.IsNilInt() {
    if !hi.IsNilInt() {
      slice = seq.contents[lo.Int():hi.Int()]
    } else {
      slice = seq.contents[lo.Int():]
    }
  } else {
    if !hi.IsNilInt() {
      slice = seq.contents[:hi.Int()]
    } else {
      slice = seq.contents
    }
  }

  return Seq{slice, seq.isString}
}

// Concat returns the concatenation of two sequences.
func (seq Seq) Concat(seq2 Seq) Seq {
  if seq.LenInt() == 0 {
    return seq2
  }
  if seq2.LenInt() == 0 {
    return seq
  }

  n, n2 := len(seq.contents), len(seq2.contents)
  newSlice := make([]interface{}, n+n2)
  copy(newSlice, seq.contents)
  copy(newSlice[len(seq.contents):], seq2.contents)
  return Seq{newSlice, seq.isString || seq2.isString}
}

// Equals compares two sequences for equality.
func (seq Seq) Equals(seq2 Seq) bool {
  return sliceEquals(seq.contents, seq2.contents)
}

// EqualsGeneric implements the EqualsGeneric interface.
func (seq Seq) EqualsGeneric(other interface{}) bool {
  seq2, ok := other.(Seq)
  return ok && seq.Equals(seq2)
}

// IsPrefixOf finds whether s[i] == s2[i] for all i < some n.
func (seq Seq) IsPrefixOf(seq2 Seq) bool {
  return sliceIsPrefixOf(seq.contents, seq2.contents)
}

// IsProperPrefixOf finds whether s[i] == s2[i] for all i < some n, and moreover
// s != s2.
func (seq Seq) IsProperPrefixOf(seq2 Seq) bool {
  return sliceIsProperPrefixOf(seq.contents, seq2.contents)
}

// UniqueElements returns the set of elements in the sequence.
func (seq Seq) UniqueElements() Set {
  return (*Builder)(&seq.contents).ToSet()
}

func (seq Seq) String() string {
  if seq.isString {
    s := ""
    for _, c := range seq.contents {
      s += c.(Char).String()
    }
    return s
  } else {
    return "[" + stringOfElements(seq.contents) + "]"
  }
}

/******************************************************************************
 * Arrays
 ******************************************************************************/

// An Array is a Go slice representing a (possibly) multidimensional array,
// along with metadata.  There aren't any methods for updating; instead, you can
// update through the pointer returned by Index.
type Array struct {
  contents []interface{} // stored as a flat one-dimensional slice
  dims     []int
}

func newArray(dims ...Int) *Array {
  intDims := make([]int, len(dims))
  size := 1
  for d := len(dims) - 1; d >= 0; d-- {
    //    sizes[d] = size
    intDims[d] = dims[d].Int()
    size *= intDims[d]
  }
  // Bypass the SeqOf constructor to avoid defensive copy
  contents := make([]interface{}, size)
  return &Array{
    contents: contents,
    dims:     intDims,
  }
}

// EmptyArray is an empty one-dimensional array.
var EmptyArray = NewArray(Zero)

// NewArray returns a new Array full of the default value of the given type.
func NewArray(dims ...Int) *Array {
  return NewArrayWithValue(nil, dims...)
}

// NewArrayWithValue returns a new Array full of the given initial value.
func NewArrayWithValue(init interface{}, dims ...Int) *Array {
  ans := newArray(dims...)
  if init != nil {
    for i := range ans.contents {
      ans.contents[i] = init
    }
  }
  return ans
}

// NewArrayWithValues returns a new one-dimensional Array with the given initial
// values.
func NewArrayWithValues(values ...interface{}) *Array {
  arr := make([]interface{}, len(values))
  copy(arr, values)
  return &Array{
    contents: arr,
    dims:     []int{len(values)},
  }
}

// Len returns the length of the array in the given dimension.
func (array *Array) Len(dim int) Int {
  return IntOf(array.LenInt(dim))
}

// LenInt returns the length of the array in the given dimension, as an int.
func (array *Array) LenInt(dim int) int {
  return array.dims[dim]
}

// Equals compares two arrays for equality.  Values are compared using
// dafny.AreEqual.
func (array *Array) Equals(array2 *Array) bool {
  if array == array2 {
    return true
  }
  if array == nil || array2 == nil {
    return false // we already know they're not equal as pointers
  }
  if len(array.dims) != len(array2.dims) {
    return false
  }
  for i, d := range array.dims {
    if d != array2.dims[i] {
      return false
    }
  }

  return sliceIsPrefixAfterLengthCheck(array.contents, array2.contents)
}

// EqualsGeneric implements the EqualsGeneric interface.
func (array *Array) EqualsGeneric(other interface{}) bool {
  array2, ok := other.(*Array)
  return ok && array.Equals(array2)
}

func (array *Array) findIndex(ixs ...int) int {
  i := 0
  size := 1
  for d := len(array.dims) - 1; d >= 0; d-- {
    i += size * ixs[d]
    size *= array.dims[d]
  }
  return i
}

// Index gets the element at the given indices into the array.
func (array *Array) Index(ixs ...Int) *interface{} {
  if len(ixs) != len(array.dims) {
    panic(fmt.Sprintf("Expected %d indices but got %d", len(array.dims), len(ixs)))
  }
  ints := make([]int, len(ixs))
  for i, ix := range ixs {
    ints[i] = ix.Int()
  }
  return array.IndexInts(ints...)
}

// IndexInts gets the element at the given indices into the array.
func (array *Array) IndexInts(ixs ...int) *interface{} {
  return &array.contents[array.findIndex(ixs...)]
}

// Iterator iterates over the array.
func (array *Array) Iterator() Iterator {
  return sliceIterator(array.contents)
}

// RangeToSeq converts the selected portion of the array to a sequence.
func (array *Array) RangeToSeq(lo, hi Int) Seq {
  if len(array.dims) != 1 {
    panic("Can't take a slice of a multidimensional array")
  }
        isString := false;
        if len(array.contents) > 0 {
            _, isString = array.contents[0].(Char)
        }

  // TODO Should set isString to true if this is an array of characters
  // Do not know if it is an array of characters if the array is empty
  seq := SeqOf(array.contents...)
        seq.isString = isString

  return seq.Subseq(lo, hi)
}

// Update updates a location in a one-dimensional array.  (Must be
// one-dimensional so that this function is uniform with the other Update
// methods.)
func (array *Array) Update(ix Int, value interface{}) {
  array.UpdateInt(ix.Int(), value)
}

// UpdateInt updates a location in a one-dimensional array.  (Must be
// one-dimensional so that this function is uniform with the other Update
// methods.)
func (array *Array) UpdateInt(ix int, value interface{}) {
  if len(array.dims) != 1 {
    panic("Can't update a multidimensional array")
  }
  array.contents[ix] = value
}

func (array *Array) stringOfSubspace(d int, ixs []int) string {
  if d == len(array.dims) {
    return String(*array.IndexInts(ixs...))
  }
  s := "["
  for i := 0; i < array.dims[d]; i++ {
    if i > 0 {
      s += ", "
    }
    ixs[d] = i
    s += array.stringOfSubspace(d+1, ixs)
  }
  s += "]"
  return s
}

func (array *Array) String() string {
  ixs := make([]int, len(array.dims))
  return array.stringOfSubspace(0, ixs)
}

/******************************************************************************
 * Tuples
 ******************************************************************************/

// A Tuple is a one-dimensional heterogeneous array.
type Tuple struct {
  contents []interface{}
}

// TupleOf creates a tuple with the given values.
func TupleOf(values ...interface{}) Tuple {
  arr := make([]interface{}, len(values))
  copy(arr, values)
  return Tuple{arr}
}

// Equals returns whether two tuples have the same values.
func (tuple Tuple) Equals(other Tuple) bool {
  return sliceEquals(tuple.contents, other.contents)
}

// EqualsGeneric implements the EqualsGeneric interface.
func (tuple Tuple) EqualsGeneric(other interface{}) bool {
  tuple2, ok := other.(Tuple)
  return ok && tuple.Equals(tuple2)
}

func (tuple Tuple) String() string {
  return "(" + stringOfElements(tuple.contents) + ")"
}

// Index looks up the address of the ith element of the tuple.
func (tuple Tuple) Index(i Int) *interface{} {
  return tuple.IndexInt(i.Int())
}

// IndexInt looks up the address of the ith element of the tuple.
func (tuple Tuple) IndexInt(i int) *interface{} {
  return &tuple.contents[i]
}

// TupleType returns the type of a tuple with given element types.
func TupleType(tys ...TypeDescriptor) TypeDescriptor {
  arr := make([]TypeDescriptor, len(tys))
  copy(arr, tys)
  return tupleType{arr}
}

type tupleType struct {
  eltTys []TypeDescriptor
}

func (tt tupleType) Default() interface{} {
  values := make([]interface{}, len(tt.eltTys))
  for i, ty := range tt.eltTys {
    values[i] = ty.Default()
  }
  return TupleOf(values...)
}

func (tt tupleType) String() string {
  s := "("
  sep := ""
  for _, ty := range tt.eltTys {
    s += sep + String(ty)
    sep = ", "
  }
  s += ")"
  return s
}

/******************************************************************************
 * Collection building
 ******************************************************************************/

// A Builder holds values as they're imperatively accumulated in order to build
// an Array, Set, or MultiSet.
type Builder []interface{}

// NewBuilder creates a new Builder.
func NewBuilder() *Builder {
  return new(Builder)
}

// Add adds a new value to a Builder.
func (builder *Builder) Add(value interface{}) {
  *builder = append(*builder, value)
}

// ToArray creates an Array with the accumulated values.
func (builder *Builder) ToArray() *Array {
  return NewArrayWithValues(*builder...)
}

// ToSet creates a Set with the accumulated values.
func (builder *Builder) ToSet() Set {
  return SetOf(*builder...)
}

// Iterator iterates over the accumulated values.
func (builder *Builder) Iterator() Iterator {
  return sliceIterator(*builder)
}

/******************************************************************************
 * Sets
 ******************************************************************************/

// A Set is a sequence without duplicates.
type Set struct {
  contents []interface{}
}

// EmptySet is the empty set.
var EmptySet = SetOf()

// SetOf creates a set with the given values.
func SetOf(values ...interface{}) Set {
  uniq := make([]interface{}, 0, len(values))
NEXT_INPUT:
  for _, v := range values {
    for _, u := range uniq {
      if AreEqual(u, v) {
        continue NEXT_INPUT
      }
    }
    uniq = append(uniq, v)
  }
  return Set{uniq}
}

// Cardinality returns the cardinality (size) of the set.
func (set Set) Cardinality() Int {
  return IntOf(set.CardinalityInt())
}

// CardinalityInt returns the cardinality (size) of the set as an int.
func (set Set) CardinalityInt() int {
  return len(set.contents)
}

// Contains returns whether the given value is an element of the set.
func (set Set) Contains(value interface{}) bool {
  return sliceContains(set.contents, value)
}

// Iterator returns an iterator over the elements of the set.
func (set Set) Iterator() Iterator {
  return sliceIterator(set.contents)
}

// Union makes a set containing each element contained by either input set.
func (set Set) Union(set2 Set) Set {
  if set.CardinalityInt() == 0 {
    return set2
  }
  if set2.CardinalityInt() == 0 {
    return set
  }

  n := set.CardinalityInt()
  uniq := make([]interface{}, n)
  copy(uniq, set.contents)
NEXT_INPUT:
  for _, v := range set2.contents {
    for _, u := range uniq {
      if AreEqual(u, v) {
        continue NEXT_INPUT
      }
    }
    uniq = append(uniq, v)
  }

  return Set{uniq}
}

// Intersection makes a set containing each element contained by both input
// sets.
func (set Set) Intersection(set2 Set) Set {
  if set.CardinalityInt() == 0 || set2.CardinalityInt() == 0 {
    return EmptySet
  }

  uniq := make([]interface{}, 0)
  for _, v := range set.contents {
    if set2.Contains(v) {
      uniq = append(uniq, v)
    }
  }

  return Set{uniq}
}

// Difference makes a set containing each element contained by set but not
// by set2.
func (set Set) Difference(set2 Set) Set {
  if set.CardinalityInt() == 0 || set2.CardinalityInt() == 0 {
    return set
  }

  elts := make([]interface{}, 0, max(0, set.CardinalityInt()-set2.CardinalityInt()))
  for _, v := range set.contents {
    if !set2.Contains(v) {
      elts = append(elts, v)
    }
  }

  return Set{elts}
}

// IsDisjointFrom returns true if the sets have no elements in common.
func (set Set) IsDisjointFrom(set2 Set) bool {
  if set.CardinalityInt() == 0 || set2.CardinalityInt() == 0 {
    return true
  }

  for _, v := range set.contents {
    if sliceContains(set2.contents, v) {
      return false
    }
  }

  return true
}

// Equals tests whether the sets contain the same elements.
func (set Set) Equals(set2 Set) bool {
  return set.CardinalityInt() == set2.CardinalityInt() &&
    set.isSubsetAfterCardinalityCheck(set2)
}

// EqualsGeneric implements the EqualsGeneric interface.
func (set Set) EqualsGeneric(other interface{}) bool {
  set2, ok := other.(Set)
  return ok && set.Equals(set2)
}

// IsSubsetOf returns true if each element in this set is also in the other.
func (set Set) IsSubsetOf(set2 Set) bool {
  return set.CardinalityInt() <= set2.CardinalityInt() &&
    set.isSubsetAfterCardinalityCheck(set2)
}

// IsProperSubsetOf returns true if each element in this set is also in the
// other, and moreover the sets aren't equal.
func (set Set) IsProperSubsetOf(set2 Set) bool {
  return set.CardinalityInt() < set2.CardinalityInt() &&
    set.isSubsetAfterCardinalityCheck(set2)
}

func (set Set) isSubsetAfterCardinalityCheck(set2 Set) bool {
  for _, v := range set.contents {
    if !sliceContains(set2.contents, v) {
      return false
    }
  }
  return true
}

// Elements returns the set of elements (i.e. the set itself).
func (set Set) Elements() Set {
  return set
}

// AllSubsets returns an iterator over all subsets of the given set.
func (set Set) AllSubsets() Iterator {
  // Use a big integer to range from 0 to 2^n
  r := new(big.Int)
  limit := new(big.Int).Lsh(One.impl, uint(set.CardinalityInt()))
  return func() (interface{}, bool) {
    if r.Cmp(limit) == 0 {
      return Set{}, false
    } else {
      values := make([]interface{}, 0, len(set.contents))
      i := 0
      s := new(big.Int).Set(r)
      mod := new(big.Int)
      for s.Cmp(Zero.impl) > 0 {
        if mod.Mod(s, Two.impl).Cmp(Zero.impl) != 0 {
          values = append(values, set.contents[i])
        }
        s.Div(s, Two.impl)
        i++
      }
      r.Add(r, One.impl)

      // Annoyingly, the other implementations reverse the order of the
      // elements, so we have to as well
      return Set{reverse(values)}, true
    }
  }
}

func reverse(values []interface{}) []interface{} {
  ans := make([]interface{}, len(values))
  n := len(values)
  for i, v := range values {
    ans[n-1-i] = v
  }
  return ans
}

func (set Set) String() string {
  return "{" + stringOfElements(set.contents) + "}"
}

/******************************************************************************
 * Multisets
 ******************************************************************************/

// A MultiSet is an unordered sequence of elements with possible duplication.
type MultiSet struct {
  elts []msetElt
}

type msetElt struct {
  value interface{}
  count Int
}

// EmptyMultiSet is the empty multiset.
var EmptyMultiSet = MultiSetOf()

// MultiSetOf creates a MultiSet with the given elements.
func MultiSetOf(values ...interface{}) MultiSet {
  elts := make([]msetElt, 0, len(values))
NEXT_INPUT:
  for _, v := range values {
    for i, u := range elts {
      if AreEqual(u.value, v) {
        elts[i] = msetElt{value: u.value, count: u.count.Plus(One)}
        continue NEXT_INPUT
      }
    }
    elts = append(elts, msetElt{value: v, count: One})
  }
  return MultiSet{elts}
}

// MultiSetFromSeq creates a MultiSet from the elements in the given sequence.
func MultiSetFromSeq(seq Seq) MultiSet {
  return MultiSetOf(seq.contents...)
}

// MultiSetFromSet creates a MultiSet from the elements in the given set.
func MultiSetFromSet(set Set) MultiSet {
  elts := make([]msetElt, len(set.contents))
  for i, v := range set.contents {
    // No need to check whether it's already there because Set elements are
    // assumed to be unique
    elts[i] = msetElt{v, One}
  }
  return MultiSet{elts}
}

func (mset MultiSet) clone() MultiSet {
  elts := make([]msetElt, len(mset.elts))
  copy(elts, mset.elts)
  return MultiSet{elts}
}

func (mset MultiSet) findIndex(value interface{}) (int, bool) {
  for i, e := range mset.elts {
    if AreEqual(e.value, value) {
      return i, true
    }
  }
  return -1, false
}

// Update changes the cardinality of the given value in the multiset, returning
// a new multiset unless the cardinality did not actually change.
func (mset MultiSet) Update(value interface{}, n Int) MultiSet {
  i, found := mset.findIndex(value)
  if found {
    if mset.elts[i].count == n {
      return mset
    } else {
      ans := mset.clone()
      ans.elts[i] = msetElt{value, n}
      return ans
    }
  } else if n.Cmp(Zero) == 0 {
    return mset
  } else {
    return MultiSet{append(mset.clone().elts, msetElt{value, n})}
  }
}

// Cardinality returns the number of elements in the multiset (counting
// repetitions).
func (mset MultiSet) Cardinality() Int {
  n := new(big.Int)
  for _, e := range mset.elts {
    n.Add(n, e.count.impl)
  }
  return intOf(n)
}

// CardinalityInt returns the number of elements in the multiset (counting
// repetitions) as an int.
func (mset MultiSet) CardinalityInt() int {
  n := 0
  for _, e := range mset.elts {
    n += e.count.Int()
  }
  return n
}

// Index returns the ith element of the multiset, which is arbitrary except that
// it is different from the jth element when i /= j.  (Repetitions are ignored.)
func (mset MultiSet) Index(i Int) interface{} {
  return mset.elts[i.Int()]
}

// Iterator returns an iterator over the multiset (including repetitions).
func (mset MultiSet) Iterator() Iterator {
  i := 0
  n := new(big.Int)
  return func() (interface{}, bool) {
    for {
      if i >= len(mset.elts) {
        return nil, false
      }
      if n.Cmp(mset.elts[i].count.impl) >= 0 {
        n.SetInt64(0)
        i++
      } else {
        break
      }
    }

    ans := mset.elts[i].value
    n.Add(n, One.impl)
    return ans, true
  }
}

// Contains returns whether the multiset contains the given element (at least
// once).
func (mset MultiSet) Contains(value interface{}) bool {
  return mset.Multiplicity(value).Cmp(Zero) > 0
}

// Multiplicity returns the number of times a given element occurs in the
// multiset.
func (mset MultiSet) Multiplicity(value interface{}) Int {
  i, found := mset.findIndex(value)
  if found {
    return mset.elts[i].count
  } else {
    return Zero
  }
}

// Elements returns an iterator that yields each element in the multiset, as
// many times as it appears.
func (mset MultiSet) Elements() func() (interface{}, bool) {
  i := 0
  n := new(big.Int)
  return func() (interface{}, bool) {
    for {
      if i >= len(mset.elts) {
        return nil, false
      }
      if n.Cmp(mset.elts[i].count.impl) == 0 {
        i++
        n.SetInt64(0)
      } else {
        break
      }
    }
    n.Add(n, One.impl)
    return mset.elts[i].value, true
  }
}

// UniqueElements returns an iterator that yields each element in the multiset
// once.
func (mset MultiSet) UniqueElements() func() (interface{}, bool) {
  i := 0
  return func() (interface{}, bool) {
    if i >= len(mset.elts) {
      return nil, false
    } else {
      i++
      return mset.elts[i-1].value, true
    }
  }
}

// Union returns a multiset including each element of either set.  Each value's
// multiplicity will be the sum of its multiplicities in the original multisets.
func (mset MultiSet) Union(mset2 MultiSet) MultiSet {
  if len(mset.elts) == 0 {
    return mset2
  }
  if len(mset2.elts) == 0 {
    return mset
  }

  elts := make([]msetElt, 0, len(mset.elts)+len(mset2.elts))
  for _, e := range mset.elts {
    if e.count.Cmp(Zero) == 0 {
      // e.value in mset2 will be added in the next separate for loop
      continue
    }
    m := mset2.Multiplicity(e.value)
    elts = append(elts, msetElt{e.value, e.count.Plus(m)})
  }
  for _, e := range mset2.elts {
    if !mset.Contains(e.value) {
      elts = append(elts, e)
    }
  }

  return MultiSet{elts}
}

// Intersection returns a multiset including those elements which occur in both
// sets.  Each value's multiplicity will be the minimum of its multiplicities
// in the original multisets.
func (mset MultiSet) Intersection(mset2 MultiSet) MultiSet {
  if len(mset.elts) == 0 || len(mset2.elts) == 0 {
    return EmptyMultiSet
  }

  elts := make([]msetElt, 0)
  for _, e := range mset.elts {
    m := mset2.Multiplicity(e.value)
    if m.Cmp(Zero) != 0 {
      elts = append(elts, msetElt{e.value, e.count.Min(m)})
    }
  }

  return MultiSet{elts}
}

// Difference returns a multiset including those elements which occur in the
// first argument but not the second.  Each value's multiplicity will be its
// multiplicity in mset minus its multiplicity in mset2.
func (mset MultiSet) Difference(mset2 MultiSet) MultiSet {
  if len(mset.elts) == 0 || len(mset2.elts) == 0 {
    return mset
  }

  elts := make([]msetElt, 0, max(0, len(mset.elts)-len(mset2.elts)))
  for _, e := range mset.elts {
    d := e.count.Minus(mset2.Multiplicity(e.value))
    if d.Cmp(Zero) > 0 {
      elts = append(elts, msetElt{e.value, d})
    }
  }

  return MultiSet{elts}
}

// IsDisjointFrom returns whether two multisets contain no elements in common.
func (mset MultiSet) IsDisjointFrom(mset2 MultiSet) bool {
  if len(mset.elts) == 0 || len(mset2.elts) == 0 {
    return true
  }

  for _, e := range mset.elts {
    if (e.count.Cmp(Zero) != 0) && mset2.Contains(e.value) {
      return false
    }
  }

  return true
}

// Equals returns whether two multisets have the same values with the same
// multiplicities.
func (mset MultiSet) Equals(mset2 MultiSet) bool {
  for _, e := range mset.elts {
    m := mset2.Multiplicity(e.value)
    if e.count.Cmp(m) != 0 {
      return false
    }
  }
  return mset.CardinalityInt() == mset2.CardinalityInt()
}

// EqualsGeneric implements the EqualsGeneric interface.
func (mset MultiSet) EqualsGeneric(other interface{}) bool {
  mset2, ok := other.(MultiSet)
  return ok && mset.Equals(mset2)
}

// IsSubsetOf returns whether one multiset has a subset of the elements of the
// other, with lesser or equal multiplicities.
func (mset MultiSet) IsSubsetOf(mset2 MultiSet) bool {
  for _, e := range mset.elts {
    m := mset2.Multiplicity(e.value)
    if e.count.Cmp(m) > 0 {
      return false
    }
  }
  return true
}

// IsProperSubsetOf returns whether one multiset has a proper subset of the
// elements of the other, with strictly lesser multiplicities.
func (mset MultiSet) IsProperSubsetOf(mset2 MultiSet) bool {
  return mset.IsSubsetOf(mset2) && mset.CardinalityInt() < mset2.CardinalityInt()
}

func (mset MultiSet) String() string {
  s := "multiset{"
  sep := ""
  i := new(big.Int)
  for _, e := range mset.elts {
    for i.SetInt64(0); i.Cmp(e.count.impl) < 0; i.Add(i, One.impl) {
      s += sep + String(e.value)
      sep = ", "
    }
  }
  s += "}"
  return s
}

/******************************************************************************
 * Maps
 ******************************************************************************/

// A Map is an association between keys and values.
type Map struct {
  elts []mapElt
}

type mapElt struct {
  key, value interface{}
}

// A MapBuilder creates a new Map by accumulating elements imperatively.
type MapBuilder []mapElt

// NewMapBuilder creates a new map builder.
func NewMapBuilder() *MapBuilder {
  return new(MapBuilder)
}

// Add adds a key and value to the map being built.
func (mb *MapBuilder) Add(k, v interface{}) *MapBuilder {
  *mb = append(*mb, mapElt{k, v})
  return mb
}

// ToMap gets the map out of the map builder.
func (mb *MapBuilder) ToMap() Map {
  return Map{*mb}
}

// EmptyMap is the empty map.
var EmptyMap = NewMapBuilder().ToMap()

func (m Map) clone() Map {
  elts := make([]mapElt, len(m.elts))
  copy(elts, m.elts)
  return Map{elts}
}

func (m Map) findIndex(key interface{}) (int, bool) {
  for i, e := range m.elts {
    if AreEqual(e.key, key) {
      return i, true
    }
  }
  return -1, false
}

// Cardinality finds the number of elements in the map.
func (m Map) Cardinality() Int {
  return IntOf(m.CardinalityInt())
}

// CardinalityInt finds the number of elements in the map as an int.
func (m Map) CardinalityInt() int {
  return len(m.elts)
}

// Find finds the given key in the map, returning it and a success flag.
func (m Map) Find(key interface{}) (interface{}, bool) {
  i, found := m.findIndex(key)
  if found {
    return m.elts[i].value, true
  } else {
    return nil, false
  }
}

// Get finds the given key in the map, returning it or nil.
func (m Map) Get(key interface{}) interface{} {
  v, _ := m.Find(key)
  return v
}

// Contains returns whether the given key is in the map.
func (m Map) Contains(key interface{}) bool {
  _, found := m.findIndex(key)
  return found
}

// Update returns a new Map which associates the given key and value.
func (m Map) Update(key, value interface{}) Map {
  ans := m.clone()
  i, found := ans.findIndex(key)
  if found {
    ans.elts[i] = mapElt{key, value}
  } else {
    ans.elts = append(ans.elts, mapElt{key, value})
  }
  return ans
}

func (a Map) Merge(b Map) Map {
  if a.CardinalityInt() == 0 {
    return b
  }
  if b.CardinalityInt() == 0 {
    return a
  }

  m := make([]mapElt, len(b.elts), len(a.elts) + len(b.elts))
  copy(m, b.elts)
  for _, e := range a.elts {
    _, found := b.findIndex(e.key)
    if !found {
      m = append(m, e)
    }
  }
  return Map{m}
}

func (a Map) Subtract(keys Set) Map {
  if a.CardinalityInt() == 0 || keys.CardinalityInt() == 0 {
    return a
  }

  mb := NewMapBuilder()
  for _, e := range a.elts {
    if !keys.Contains(e.key) {
      *mb = append(*mb, e)
    }
  }
  return mb.ToMap()
}

// Equals returns whether each map associates the same keys to the same values.
func (m Map) Equals(m2 Map) bool {
  if len(m.elts) != len(m2.elts) {
    return false
  }
  for _, e := range m.elts {
    i, found := m2.findIndex(e.key)
    if !found || !AreEqual(e.value, m2.elts[i].value) {
      return false
    }
  }
  return true
}

// EqualsGeneric implements the EqualsGeneric interface.
func (m Map) EqualsGeneric(other interface{}) bool {
  m2, ok := other.(Map)
  return ok && m.Equals(m2)
}

// Keys returns the set of keys in the map.
func (m Map) Keys() Set {
  b := NewBuilder()
  for _, e := range m.elts {
    b.Add(e.key)
  }
  return b.ToSet()
}

// Values returns the set of values in the map.
func (m Map) Values() Set {
  b := NewBuilder()
  for _, e := range m.elts {
    b.Add(e.value)
  }
  return b.ToSet()
}

// Items returns the set of items in the map as a Set of Tuples.
func (m Map) Items() Set {
  b := NewBuilder()
  for _, e := range m.elts {
    b.Add(TupleOf(e.key, e.value))
  }
  return b.ToSet()
}

func (m Map) String() string {
  s := "map["
  for i, e := range m.elts {
    if i > 0 {
      s += ", "
    }
    s += fmt.Sprintf("%s := %s", String(e.key), String(e.value))
  }
  s += "]"
  return s
}

/******************************************************************************
 * Integers
 ******************************************************************************/

// An Int is an immutable big integer.
type Int struct {
  impl *big.Int
  // debug string
} // Careful not to mutate!

// A BV is an immutable big bitvector (presumed to be non-negative).
type BV = Int

func intOf(i *big.Int) Int {
  return Int{
    impl: i,
    // debug: i.String(),
  }
}

// IntOf turns the given int into an Int.  Common values are cached.  This is
// simply a shorter form of IntOfInt.
func IntOf(i int) Int {
  return IntOfInt(i)
}

// IntOfInt turns the given int into an Int.  Common values are cached.
func IntOfInt(i int) Int {
  return IntOfInt64(int64(i))
}

// IntOfInt8 turns the given int8 into an Int.  Common values are cached.
func IntOfInt8(i int8) Int {
  return IntOfInt64(int64(i))
}

// IntOfInt16 turns the given int16 into an Int.  Common values are cached.
func IntOfInt16(i int16) Int {
  return IntOfInt64(int64(i))
}

// IntOfInt32 turns the given int32 into an Int.  Common values are cached.
func IntOfInt32(i int32) Int {
  return IntOfInt64(int64(i))
}

// IntOfInt64 turns the given int64 into an Int.  Common values are cached.
func IntOfInt64(i int64) Int {
  switch i {
  case -1:
    return NegativeOne
  case 0:
    return Zero
  case 1:
    return One
  case 2:
    return Two
  case 5:
    return Five
  case 10:
    return Ten
  default:
    return intOf(big.NewInt(i))
  }
}

// IntOfUint turns the given uint into an Int.  Common values are cached.
func IntOfUint(i uint) Int {
  return IntOfUint64(uint64(i))
}

// IntOfUint8 turns the given uint8 into an Int.  Common values are cached.
func IntOfUint8(i uint8) Int {
  return IntOfUint64(uint64(i))
}

// IntOfUint16 turns the given uint16 into an Int.  Common values are cached.
func IntOfUint16(i uint16) Int {
  return IntOfUint64(uint64(i))
}

// IntOfUint32 turns the given uint32 into an Int.  Common values are cached.
func IntOfUint32(i uint32) Int {
  return IntOfUint64(uint64(i))
}

// IntOfUint64 turns the given uint64 into an Int.  Common values are cached.
func IntOfUint64(i uint64) Int {
  switch i {
  case 0:
    return Zero
  case 1:
    return One
  case 2:
    return Two
  case 5:
    return Five
  case 10:
    return Ten
  default:
    return intOf(new(big.Int).SetUint64(i))
  }
}

// IntOfString parses the given string as an Int, panicking on failure.
func IntOfString(s string) Int {
  switch s {
  case "-1":
    return NegativeOne
  case "0":
    return Zero
  case "1":
    return One
  case "2":
    return Two
  case "5":
    return Five
  case "10":
    return Ten
  default:
    i, ok := new(big.Int).SetString(s, 0)
    if !ok {
      panic("Unable to parse string as int: " + s)
    } else {
      return intOf(i)
    }
  }
}

// IntOfAny converts from many different things to Int.  Note that
// switch-on-type does a linear search, so this can be slow for less common
// cases.
func IntOfAny(x interface{}) Int {
  switch x := x.(type) {
  // Try and put the most common cases earliest.
  case Int:
    return x
  case int:
    return IntOfInt(x)
  case string:
    return IntOfString(x)
  case uint:
    return IntOfUint(x)
  case Char:
    return IntOfInt32(rune(x))
  case int32:
    return IntOfInt32(x)
  case int64:
    return IntOfInt64(x)
  case uint32:
    return IntOfUint32(x)
  case uint64:
    return IntOfUint64(x)
  case int8:
    return IntOfInt8(x)
  case uint8:
    return IntOfUint8(x)
  case int16:
    return IntOfInt16(x)
  case uint16:
    return IntOfUint16(x)
  default:
    panic(fmt.Errorf("unexpected type for IntToAny: %v", refl.TypeOf(x)))
  }
}

// Int converts back into an int.  If the result is not within int range,
// the value is undefined.
func (i Int) Int() int {
  return int(i.impl.Int64())
}

// Int8 converts back into an int8.  If the result is not within int8 range,
// the value is undefined.
func (i Int) Int8() int8 {
  return int8(i.impl.Int64())
}

// Int16 converts back into an int16.  If the result is not within int16 range,
// the value is undefined.
func (i Int) Int16() int16 {
  return int16(i.impl.Int64())
}

// Int32 converts back into an int32.  If the result is not within int32 range,
// the value is undefined.
func (i Int) Int32() int32 {
  return int32(i.impl.Int64())
}

// Int64 converts back to an int64.  If the result is not within int64 range,
// the value is undefined.
func (i Int) Int64() int64 {
  return i.impl.Int64()
}

// Uint converts back to a uint.  If the result is not within uint range, the
// value is undefined.
func (i Int) Uint() uint {
  return uint(i.impl.Uint64())
}

// Uint8 converts back to a uint8.  If the result is not within uint8 range, the
// value is undefined.
func (i Int) Uint8() uint8 {
  return uint8(i.impl.Uint64())
}

// Uint16 converts back to a uint16.  If the result is not within uint16 range,
// the value is undefined.
func (i Int) Uint16() uint16 {
  return uint16(i.impl.Uint64())
}

// Uint32 converts back to a uint32.  If the result is not within uint32 range,
// the value is undefined.
func (i Int) Uint32() uint32 {
  return uint32(i.impl.Uint64())
}

// Uint64 converts back to a uint64.  If the result is not within uint64 range,
// the value is undefined.
func (i Int) Uint64() uint64 {
  return i.impl.Uint64()
}

func (i Int) String() string {
  return i.impl.String()
}

// NegativeOne is the constant -1.
var NegativeOne = intOf(big.NewInt(-1))

// Zero is the constant 0.
var Zero = intOf(big.NewInt(0))

// One is the constant 1.
var One = intOf(big.NewInt(1))

// Two is the constant 2.
var Two = intOf(big.NewInt(2))

// Five is the constant 5.
var Five = intOf(big.NewInt(5))

// Ten is the constant 10.
var Ten = intOf(big.NewInt(10))

// NilInt is a missing int value.
var NilInt = intOf(nil)

// IsNilInt returns whether this Int is actually a missing value.
func (i Int) IsNilInt() bool {
  return i.impl == nil
}

func (i Int) binOp(j Int, f func(*big.Int, *big.Int, *big.Int) *big.Int) Int {
  return intOf(f(new(big.Int), i.impl, j.impl))
}

// Plus adds two Ints.
func (i Int) Plus(j Int) Int {
  return i.binOp(j, (*big.Int).Add)
}

// Minus subtracts one Int from another.
func (i Int) Minus(j Int) Int {
  return i.binOp(j, (*big.Int).Sub)
}

// Times multiplies two Ints.
func (i Int) Times(j Int) Int {
  return i.binOp(j, (*big.Int).Mul)
}

// DivBy divides one Int by another.  (So named to distinguish from
// big.Int.Div(), which is an in-place operation.)
func (i Int) DivBy(j Int) Int {
  return i.binOp(j, (*big.Int).Div)
}

// Modulo takes the remainder when dividing one Int by another.  (So named to
// distinguish from big.Int.Mod(), which performs the operation in place.)
func (i Int) Modulo(j Int) Int {
  return i.binOp(j, (*big.Int).Mod)
}

// Negated negates an Int.
func (i Int) Negated() Int {
  return intOf(new(big.Int).Neg(i.impl))
}

// Lsh performs a left shift.
func (i Int) Lsh(j Int) Int {
  return intOf(new(big.Int).Lsh(i.impl, uint(j.Uint64())))
}

// Rsh performs a right shift.
func (i Int) Rsh(j Int) Int {
  return intOf(new(big.Int).Rsh(i.impl, uint(j.Uint64())))
}

// Lrot performs a left rotate on a BV with width w.
func (i BV) Lrot(j Int, w uint) BV {
  // (i <<< j) == ((i << j) % 2^w) | (i >> (w-j))

  ju := uint(j.Uint64())
  l := new(big.Int).Lsh(i.impl, ju)
  modulus := new(big.Int).Lsh(One.impl, w)
  l.Mod(l, modulus)
  r := modulus.Rsh(i.impl, w-ju) // reuse memory from modulus
  return intOf(l.Or(l, r))
}

// Rrot performs a right rotate on a BV with width w.
func (i BV) Rrot(j BV, w uint) BV {
  // (i >>> j) == ((i << (w-j)) % 2^w) | (i >> j)

  ju := uint(j.Uint64())
  l := new(big.Int).Lsh(i.impl, w-ju)
  modulus := new(big.Int).Lsh(One.impl, w)
  l.Mod(l, modulus)
  r := modulus.Rsh(i.impl, ju) // reuse memory from modulus
  return intOf(l.Or(l, r))
}

// Cmp compares two Ints, returning -1 for less, 0 for equal, or 1 for greater.
func (i Int) Cmp(j Int) int {
  return i.impl.Cmp(j.impl)
}

// Sign returns the sign of an Int, returning -1 for negative, 0 for zero, or
// 1 for positive.
func (i Int) Sign() int {
  return i.impl.Sign()
}

// EqualsGeneric compares an int to another value.
func (i Int) EqualsGeneric(other interface{}) bool {
  j, ok := other.(Int)
  return ok && i.Cmp(j) == 0
}

// Min returns the minimum of two integers.
func (i Int) Min(j Int) Int {
  if i.Cmp(j) <= 0 {
    return i
  } else {
    return j
  }
}

// Max returns the maximum of two integers.
func (i Int) Max(j Int) Int {
  if i.Cmp(j) >= 0 {
    return i
  } else {
    return j
  }
}

// And performs bitwise AND.
func (i Int) And(j Int) Int {
  return i.binOp(j, (*big.Int).And)
}

// Or performs bitwise OR.
func (i Int) Or(j Int) Int {
  return i.binOp(j, (*big.Int).Or)
}

// Xor performs bitwise XOR.
func (i Int) Xor(j Int) Int {
  return i.binOp(j, (*big.Int).Xor)
}

// Not performs bitwise NOT.
func (i Int) Not() Int {
  return intOf(new(big.Int).Not(i.impl))
}

func (i Int) isPowerOf10() (bool, int) {
  if i.Cmp(Zero) != 1 {
    return false, -1
  }
  n := 0
  j := i
  for {
    if j.Cmp(One) == 0 {
      return true, n
    } else if j.Modulo(Ten).Cmp(Zero) != 0 {
      return false, -1
    } else {
      j = j.DivBy(Ten)
      n++
    }
  }
}

func (i Int) dividesAPowerOf10() (yes bool, factor Int, log10 int) {
  if i.Cmp(Zero) != 1 {
    return false, Zero, -1
    // okay, so technically you could multiply by a
    // negative number, but that's not useful to
    // Real.String().
  }
  n := 0
  j := i
  fact := One
  for {
    if j.Cmp(One) == 0 {
      return true, One, n
    } else if j.Modulo(Ten).Cmp(Zero) != 0 {
      if j.Modulo(Five).Cmp(Zero) == 0 {
        for {
          fact = fact.Times(Two)
          j = j.DivBy(Five)
          n++
          if j.Cmp(One) == 0 {
            return true, fact, n
          } else if j.Modulo(Five).Cmp(Zero) != 0 {
            return false, NegativeOne, -1
          }
        }
      } else if j.Modulo(Two).Cmp(Zero) == 0 {
        for {
          fact = fact.Times(Five)
          j = j.DivBy(Two)
          n++
          if j.Cmp(One) == 0 {
            return true, fact, n
          } else if j.Modulo(Two).Cmp(Zero) != 0 {
            return false, NegativeOne, -1
          }
        }
      } else {
        return false, NegativeOne, -1
      }
    } else {
      j = j.DivBy(Ten)
      n++
    }
  }
}

// IntegerRange returns an iterator over the integers from lo up to (but not
// including) hi.
func IntegerRange(lo, hi Int) Iterator {
  if lo.impl != nil {
    i := lo
    return func() (interface{}, bool) {
      if hi.impl != nil && i.Cmp(hi) >= 0 {
        return nil, false
      } else {
        ans := i
        i = i.Plus(One)
        return ans, true
      }
    }
  } else if hi.impl != nil {
    i := hi
    return func() (interface{}, bool) {
      ans := i
      i = i.Minus(One)
      return ans, true
    }
  } else {
    return AllIntegers()
  }
}

// AllIntegers returns an iterator over all integers, starting at zero and
// alternating between positive and negative.
func AllIntegers() Iterator {
  type phase int
  const (
    zeroPhase int = iota
    posPhase
    negPhase
  )

  i := Zero
  p := zeroPhase

  return func() (interface{}, bool) {
    switch p {
    case zeroPhase:
      i = One
      p = posPhase
      return Zero, true
    case posPhase:
      p = negPhase
      return i, true
    case negPhase:
      ans := i.Negated()
      i = i.Plus(One)
      p = posPhase
      return ans, true
    default:
      panic("unknown phase")
    }
  }
}

/******************************************************************************
 * Ordinals
 ******************************************************************************/

// An Ord is an immutable big integer (presumed to be non-negative).
type Ord = Int

// IsLimitOrd returns true for a limit ordinal.
func (ord Ord) IsLimitOrd() bool {
  return ord.Cmp(Zero) == 0
}

// IsSuccOrd returns true for a successor ordinal.
func (ord Ord) IsSuccOrd() bool {
  return ord.Cmp(Zero) > 0
}

// OrdOffset returns the ordinal as an Int.
func (ord Ord) OrdOffset() Int {
  return ord
}

// IsNatOrd returns true if the ordinal represents a natural number.
func (Ord) IsNatOrd() bool {
  return true // at run time, every ORDINAL is a natural number
}

/******************************************************************************
 * Reals
 ******************************************************************************/

// A Real is an arbitrary-precision real number, represented as a ratio of
// arbitrary-precision integers.
type Real struct {
  impl *big.Rat
  // debug string
}

func realOf(r *big.Rat) Real {
  return Real{
    impl: r,
    // debug: r.String()
  }
}

// RealOf converts a float64 into a Real.  Common values are cached.
func RealOf(f float64) Real {
  if f == 0.0 {
    return ZeroReal
  }
  return realOf(new(big.Rat).SetFloat64(f))
}

// RealOfFrac makes a Real of the ratio of two Ints.
func RealOfFrac(num, denom Int) Real {
  if num.Cmp(Zero) == 0 {
    return ZeroReal
  }
  return realOf(new(big.Rat).SetFrac(num.impl, denom.impl))
}

// ZeroReal is the Real value zero.
var ZeroReal = realOf(new(big.Rat))

// NilReal is a missing Real value.
var NilReal = realOf(nil)

// IsNilReal returns whether this is actually a missing value.
func (x Real) IsNilReal() bool {
  return x.impl == nil
}

// RealOfString parses the given string in base 10 and panics if this is not
// possible.
func RealOfString(s string) Real {
  x, ok := new(big.Rat).SetString(s)
  if !ok {
    panic("Can't parse generated string as ratio: \"" + s + "\"")
  }
  if x.Cmp(ZeroReal.impl) == 0 {
    return ZeroReal
  }
  return realOf(x)
}

// Int converts the given real to an integer, rounding toward negative numbers.
// (That is, returns floor(x).)
func (x Real) Int() Int {
  if x.Cmp(ZeroReal) == 0 || x.Denom().Cmp(One) == 0 {
    return x.Num()
  } else if x.Num().Cmp(Zero) > 0 {
    return intOf(new(big.Int).Div(x.impl.Num(), x.impl.Denom()))
  } else {
    a := new(big.Int).Sub(x.impl.Num(), x.impl.Denom())
    a.Add(a, One.impl)
    return intOf(a.Quo(a, x.impl.Denom())) // note: *truncated* division
  }
}

// Num returns the given Real's numerator as an Int
func (x Real) Num() Int {
  return intOf(x.impl.Num())
}

// Denom returns the given Real's denominator as an Int
func (x Real) Denom() Int {
  return intOf(x.impl.Denom())
}

func (x Real) String() string {
  if x.Num().Cmp(Zero) == 0 || x.Denom().Cmp(One) == 0 {
    return x.Num().String() + ".0"
  }
  divsPow10, fact, log10 := x.Denom().dividesAPowerOf10()
  if divsPow10 {
    num := x.Num().Times(fact)
    var sign, digits string
    if x.Cmp(ZeroReal) < 0 {
      sign, digits = "-", num.Negated().String()
    } else {
      sign, digits = "", num.String()
    }
    if log10 < len(digits) {
      n := len(digits) - log10
      return sign + digits[0:n] + "." + digits[n:]
    } else {
      s := sign + "0."
      for i := 0; i < log10-len(digits); i++ {
        s = s + "0"
      }
      return s + digits
    }
  } else {
    return "(" + x.Num().String() + ".0 / " + x.Denom().String() + ".0)"
  }
}

func (x Real) isPowerOf10() (bool, int) {
  if x.Num().Cmp(Zero) != 1 {
    return false, -1
  } else if x.Num().Cmp(One) == 1 {
    b, i := x.Denom().isPowerOf10()
    return b, -i
  } else if x.Denom().Cmp(One) != 1 {
    return false, -1
  } else {
    return x.Num().isPowerOf10()
  }
}

// binOp lifts a binary operation on *big.Rat to one on Reals.  The second
// argument is intended to be of the form (*big.Rat).Op.
func (x Real) binOp(y Real, f func(*big.Rat, *big.Rat, *big.Rat) *big.Rat) Real {
  return realOf(f(new(big.Rat), x.impl, y.impl))
}

// Plus adds two Reals.
func (x Real) Plus(y Real) Real {
  return x.binOp(y, (*big.Rat).Add)
}

// Minus subtracts one Real from another.
func (x Real) Minus(y Real) Real {
  return x.binOp(y, (*big.Rat).Sub)
}

// Times multiplies two Reals.
func (x Real) Times(y Real) Real {
  return x.binOp(y, (*big.Rat).Mul)
}

// DivBy divides one Real by another.
func (x Real) DivBy(y Real) Real {
  return x.binOp(y, (*big.Rat).Quo)
}

// Cmp compares one Real to another, returning -1 for less, 0 for equal, or 1
// for greater.
func (x Real) Cmp(y Real) int {
  return x.impl.Cmp(y.impl)
}

// Sign returns the sign of a Real, returning -1 for negative, 0 for zero, or
// 1 for positive.
func (x Real) Sign() int {
  return x.impl.Sign()
}

// EqualsGeneric compares an int to another value.
func (x Real) EqualsGeneric(other interface{}) bool {
  y, ok := other.(Real)
  return ok && x.Cmp(y) == 0
}

// Min returns the minimum of two reals.
func (x Real) Min(y Real) Real {
  if x.Cmp(y) <= 0 {
    return x
  } else {
    return y
  }
}

// Max returns the maximum of two reals.
func (x Real) Max(y Real) Real {
  if x.Cmp(y) >= 0 {
    return x
  } else {
    return y
  }
}

/******************************************************************************
 * Native math
 ******************************************************************************/

// DivInt does Euclidean division on the given ints
func DivInt(x int, y int) int {
  if x >= 0 {
    if y >= 0 {
      return x / y
    } else {
      return -(x / -y)
    }
  } else {
    if y >= 0 {
      return -((-x - 1) / y) - 1
    } else {
      return ((-x - 1) / (-y)) + 1
    }
  }
}

// DivInt8 does Euclidean divison on the given int8s
func DivInt8(x int8, y int8) int8 {
  if x >= 0 {
    if y >= 0 {
      return x / y
    } else {
      return -(x / -y)
    }
  } else {
    if y >= 0 {
      return -((-x - 1) / y) - 1
    } else {
      return ((-x - 1) / (-y)) + 1
    }
  }
}

// DivInt16 does Euclidean divison on the given int16s
func DivInt16(x int16, y int16) int16 {
  if x >= 0 {
    if y >= 0 {
      return x / y
    } else {
      return -(x / -y)
    }
  } else {
    if y >= 0 {
      return -((-x - 1) / y) - 1
    } else {
      return ((-x - 1) / (-y)) + 1
    }
  }
}

// DivInt32 does Euclidean divison on the given int32s
func DivInt32(x int32, y int32) int32 {
  if x >= 0 {
    if y >= 0 {
      return x / y
    } else {
      return -(x / -y)
    }
  } else {
    if y >= 0 {
      return -((-x - 1) / y) - 1
    } else {
      return ((-x - 1) / (-y)) + 1
    }
  }
}

// DivInt64 does Euclidean divison on the given int64s
func DivInt64(x int64, y int64) int64 {
  if x >= 0 {
    if y >= 0 {
      return x / y
    } else {
      return -(x / -y)
    }
  } else {
    if y >= 0 {
      return -((-x - 1) / y) - 1
    } else {
      return ((-x - 1) / (-y)) + 1
    }
  }
}

// DivFloat32 does Euclidean division on the given float32s
func DivFloat32(x float32, y float32) float32 {
  if x >= 0 {
    if y >= 0 {
      return x / y
    } else {
      return -(x / -y)
    }
  } else {
    if y >= 0 {
      return -((-x - 1) / y) - 1
    } else {
      return ((-x - 1) / (-y)) + 1
    }
  }
}

// DivFloat64 does Euclidean division on the given float64s
func DivFloat64(x float64, y float64) float64 {
  if x >= 0 {
    if y >= 0 {
      return x / y
    } else {
      return -(x / -y)
    }
  } else {
    if y >= 0 {
      return -((-x - 1) / y) - 1
    } else {
      return ((-x - 1) / (-y)) + 1
    }
  }
}

// LrotUint performs left rotation on the low w bits of an int
func LrotUint(x uint, n Int, w uint) uint {
  y := n.Uint()
  return ((x << y) % (1 << w)) | (x >> (w - y))
}

// LrotUint8 performs left rotation on the low w bits of an int8
func LrotUint8(x uint8, n Int, w uint) uint8 {
  y := n.Uint()
  return ((x << y) % (1 << w)) | (x >> (w - y))
}

// LrotUint16 performs left rotation on the low w bits of an int16
func LrotUint16(x uint16, n Int, w uint) uint16 {
  y := n.Uint()
  return ((x << y) % (1 << w)) | (x >> (w - y))
}

// LrotUint32 performs left rotation on the low w bits of an int32
func LrotUint32(x uint32, n Int, w uint) uint32 {
  y := n.Uint()
  return ((x << y) % (1 << w)) | (x >> (w - y))
}

// LrotUint64 performs left rotation on the low w bits of an int64
func LrotUint64(x uint64, n Int, w uint) uint64 {
  y := n.Uint()
  return ((x << y) % (1 << w)) | (x >> (w - y))
}

// ModInt finds Euclidean remainder of the given ints
func ModInt(x int, y int) int {
  if y < 0 {
    y = -y
  }
  if x >= 0 {
    return x % y
  } else {
    z := (-x) % y
    if z == 0 {
      return 0
    } else {
      return y - z
    }
  }
}

// ModInt8 finds Euclidean remainder of the given int8s
func ModInt8(x int8, y int8) int8 {
  if y < 0 {
    y = -y
  }
  if x >= 0 {
    return x % y
  } else {
    z := (-x) % y
    if z == 0 {
      return 0
    } else {
      return y - z
    }
  }
}

// ModInt16 finds Euclidean remainder of the given int16s
func ModInt16(x int16, y int16) int16 {
  if y < 0 {
    y = -y
  }
  if x >= 0 {
    return x % y
  } else {
    z := (-x) % y
    if z == 0 {
      return 0
    } else {
      return y - z
    }
  }
}

// ModInt32 finds Euclidean remainder of the given int32s
func ModInt32(x int32, y int32) int32 {
  if y < 0 {
    y = -y
  }
  if x >= 0 {
    return x % y
  } else {
    z := (-x) % y
    if z == 0 {
      return 0
    } else {
      return y - z
    }
  }
}

// ModInt64 finds Euclidean remainder of the given int64s
func ModInt64(x int64, y int64) int64 {
  if y < 0 {
    y = -y
  }
  if x >= 0 {
    return x % y
  } else {
    z := (-x) % y
    if z == 0 {
      return 0
    } else {
      return y - z
    }
  }
}

// RrotUint performs right rotation on the low w bits of an int
func RrotUint(x uint, n Int, w uint) uint {
  y := n.Uint()
  return (x >> y) | ((x << (w - y)) % (1 << w))
}

// RrotUint8 performs right rotation on the low w bits of an int8
func RrotUint8(x uint8, n Int, w uint) uint8 {
  y := n.Uint()
  return (x >> y) | ((x << (w - y)) % (1 << w))
}

// RrotUint16 performs right rotation on the low w bits of an int16
func RrotUint16(x uint16, n Int, w uint) uint16 {
  y := n.Uint()
  return (x >> y) | ((x << (w - y)) % (1 << w))
}

// RrotUint32 performs right rotation on the low w bits of an int32
func RrotUint32(x uint32, n Int, w uint) uint32 {
  y := n.Uint()
  return (x >> y) | ((x << (w - y)) % (1 << w))
}

// RrotUint64 performs right rotation on the low w bits of an int64
func RrotUint64(x uint64, n Int, w uint) uint64 {
  y := n.Uint()
  return (x >> y) | ((x << (w - y)) % (1 << w))
}

/******************************************************************************
 * Hacks for generated code
 ******************************************************************************/

// The Dummy__ type, which each compiled Dafny module declares, is just so that
// we can generate "var _ dafny.Dummy__" to suppress the unused-import error.
type Dummy__ struct{}

/******************************************************************************
 * Utility functions
 ******************************************************************************/

func min(n, m int) int {
  if n <= m {
    return n
  } else {
    return m
  }
}

func max(n, m int) int {
  if n >= m {
    return n
  } else {
    return m
  }
}

func CatchHalt() {
  if r := recover(); r != nil {
    fmt.Println("[Program halted]", r)
  }
}
