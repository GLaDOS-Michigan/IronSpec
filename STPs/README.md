# Specification Testing Proof(s)

The automation provided by the Automatic Sanity Checker(ASC), and mutation testing only provide **hints** of potential specification bugs. To exhonerate or show that a hint indicates a specification bug requires manual effort - STPs adopt "Unit-Like" Tests to help answer these context specific questions in the world of specifications.

### Types of STPS

There are 4 classes of STPS: Usefulness, Provability, Correctness, and Counterexample. 


| STP             | Focus   | 
| :----------------     | :------: |
| Usefulness                   |  “Are the Preconditions Useful?” —Accept all Intended Valid Input  | 
| Provability                  |  “Are the Preconditions Strong enough?” —Reject All Intended Invalid Input. “Are the Postconditions Weak enough?” —Accept All Intended Valid Output   | 
| Correctness         |  “Are the Postconditions Correct?” —Reject All Intended Invalid Output  | 
| Counterexample    |  Valid Input/Output is Rejected. Invalid Input/Output is Accepted  | 


Each follow the general forms:

```
lemma PreconditionSTP(in:InType)
    requires TestInputProperty(in)
    ensures Precondition(in) // or !Precondition(in)
```

```
lemma PostconditionSTP(in:InType,out:OutType)
    requires TestInputProperty(in,out)
    ensures Precondition(in)
    ensures Postcondition(in,out) // or !Postcondition(in,out)
```