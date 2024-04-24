
include "./maxSpec.dfy"

module maxTest{

   import opened maxExample 

    lemma maxT(a:int,b:int) returns (c:int)
        ensures maxSpec(a,b,c)
    {
        if(a > b){
            c := a;
        }else if(b > a){
            c := b;
        }else{
            c := a + 100;
        }
    }

}

