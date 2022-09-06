include "ModulesValue.dfy"

module Hose refines GreedyAlgorithmValue {
  type Input = (seq<nat>, nat)
  type Elem = nat

  class InputA ... {
    var holes: array<nat>;
    var l_patch: nat;

    constructor (h:array<nat>,p:nat)
    {
      holes := h;
      l_patch := p;
      Repr := {this,holes};
    }
    
    predicate Valid()
    {
      Repr == {this, this.holes}
    }
  }

  class OutputA ... {
    var sol: array<Elem>;
    var patches: nat;
    var size: nat;

    constructor (x:InputA)
      requires x.Valid()
      ensures forall z | z in Repr :: fresh(z)
      ensures Valid(x)
    {
      sol := new Elem[x.holes.Length];
      Repr := {this,sol};
      patches := 0;
      size := 0;
    }

    predicate Valid(x:InputA)
    {
      Repr == {this, sol} &&
      sol.Length == x.holes.Length &&
      0 <= size <= sol.Length &&
      patches == size
    }
  }

  //NEEDED FUNCTIONS

  predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
  }
  
  predicate ssorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
  }

  //PREDICATES

  function solutionValue(x: Input, s: Solution): nat
  {
    |s|
  }

  predicate isValidInput(x: Input)
  {
    ssorted(x.0) && |x.0| > 0
  }

  function inputTrans(x:InputA) : Input
  {
    (x.holes[..],x.l_patch)
  }

  function outputTrans(x:InputA,y:OutputA) : Solution
  {
    (y.sol)[..y.size]
  }

  //---------- 1. IS SOLUTION ----------

  predicate isSolution(x:Input, s:Solution)
  {
    sorted(s) && (forall i | i in x.0 :: covered(x,s,i))
  }

  predicate covered(x:Input, s:Solution, i:nat)
  {
    exists j :: j in s && (j <= i) && (j + x.1 >= i)
  }

  //---------- 1.1. EXISTENCE OF SOLUTION ----------

  lemma existsSolution(x:Input)
  {
    var sol := x.0;
    assert isSolution(x,sol);
  }

  //---------- 2. IS BETTER SOLUTION ----------

  predicate isBetterSol(x:Input, s1:Solution, s2:Solution)

  lemma isBetterSolTrans(x:Input, s1:Solution, s2:Solution, s3:Solution)

  lemma isBetterSolRefl(x:Input, s:Solution)

  //---------- 3. IS GREEDY SOLUTION ----------

  predicate isSolGreedy(x:Input, s:Solution)
  {
    //the patches start where there is a hole
    (forall i | i in s :: i in x.0) &&
    //there is no hole covered by more than one patch
    (forall i,j | 0 <= i < j < |s| :: s[i] + x.1 < s[j])
  }

  //---------- 4. IS OPTIMAL SOLUTION ----------

  predicate isSolOptimal(x:Input, s:Solution)

  lemma betterThanOptimal(x:Input, s:Solution, optimalS:Solution)

  //---------- 5. ALGORITHM ----------

  method greedy(x:InputA) returns (res:OutputA)
  {
    res := new OutputA(x);
    res.sol[0] := x.holes[0];
    res.patches := 1;
    res.size := 1;
    var i := 1;
    var isCovered := res.sol[0] + x.l_patch;

    while (i < x.holes.Length)
      decreases (x.holes).Length - i
      invariant 0 < res.size <= i <= x.holes.Length == res.sol.Length
      invariant isCovered == res.sol[res.size-1] + x.l_patch
      //isSolution
      invariant sorted(res.sol[..res.size])
      invariant res.sol[res.size-1] in res.sol[..res.size] && res.sol[res.size-1] <= x.holes[i-1] && isCovered >= x.holes[i-1]
      invariant forall m | m in x.holes[..i] :: covered(inputTrans(x),res.sol[..res.size],m)
      invariant isSolution((x.holes[..i],x.l_patch),res.sol[..res.size])
      invariant isSolGreedy((x.holes[..i],x.l_patch),res.sol[..res.size])
      //To be able to fill the solution array
      invariant forall z | z in res.Repr :: fresh(z)
      invariant res.Valid(x)
      {
        if x.holes[i] > isCovered { //We need a new patch
          res.sol[res.size] := x.holes[i];
          res.size := res.size + 1;
          res.patches := res.patches + 1;
          isCovered := res.sol[res.size-1] + x.l_patch;

          forall m | m in x.holes[..i+1] 
           ensures covered(inputTrans(x),res.sol[..res.size],m)        
           {   
            if (m in x.holes[..i]) {
              assert covered(inputTrans(x),res.sol[..res.size-1],m);
              var j :| j in res.sol[..res.size-1] && (j <= m) && (j + inputTrans(x).1 >= m);
              assert j in res.sol[..res.size];
              assert covered(inputTrans(x),res.sol[..res.size],m);
            }
            else {
              assert x.holes[i] in res.sol[..res.size];
              //assert covered(inputTrans(x),res.sol[..res.size],x.holes[i]);
            }
           }
      }
      i := i+1;
    }

    assert x.holes[..i] == x.holes[..];

    assert isSolution(inputTrans(x),outputTrans(x,res));
    assert isSolGreedy(inputTrans(x),outputTrans(x,res));
  }

  //---------- 6. VERIFICATION ----------

  ghost method endReduction(x:Input, greedy:Solution, optimal:Solution) returns (optimal':Solution)
  {
    optimal' := optimal;
    sameSol(x,optimal',greedy);
    assert optimal' == greedy;
    assert isBetterSol(x,greedy,optimal);
  }

  lemma sameSol(x:Input, sol1:Solution, sol2:Solution)
  requires isValidInput(x)
  requires isSolution(x,sol1) && isSolution(x,sol2)
  requires isSolOptimal(x,sol1) && isSolGreedy(x,sol2)
  requires |sol1| <= |sol2|
  requires sol1 == sol2[..|sol1|]
  ensures |sol1| == |sol2|
  ensures sol1 == sol2
  {
    if |sol1| == |sol2| {}
    else {
      if (forall i,j | 0 <= i < j < |sol2| :: sol2[i] + x.1 < sol2[j]) {
        assert forall i | i in x.0 :: covered(x,sol2[..|sol1|],i);
        assert forall i | i in x.0 :: !covered(x,sol2[|sol1|..],i);
        assert forall i | i in sol2[|sol1|..] :: i !in x.0;
        assert sol2[|sol1|] in sol2;
        assert exists i :: i in sol2 && i !in x.0;
        //assert !(forall m | m in sol2 :: m in x.0);
        //assert !isSolGreedy(x,sol2);
      }
      else {
        //assert !isSolGreedy(x,sol2);
      }
    }
  }

  ghost method reduction_step(x:Input, greedy:Solution, optimal:Solution, i:nat) returns (optimal':Solution)
  {
    if (greedy[i]<optimal[i])
    { //Impossible
      assert !covered(x,optimal[..i],greedy[i]);
      assert !covered(x,optimal,greedy[i]); 
      assert greedy[i] !in x.0;

      assert !isSolGreedy(x,greedy);
    }
    else
    { //postpone where I put the patch
      optimal' := postpone(x,optimal,i,greedy[i]);
    }
  }

  //---------- 7. SWAP LEMMA ----------

  ghost method postpone(x:Input, v:Solution, i: nat, j:nat) returns (v_modified:Solution)
  requires isValidInput(x)
  requires isSolution(x,v) && isSolOptimal(x,v)
  requires 0 <= i < |v| && v[i] < j
  requires j in x.0
  requires forall p | v[i] <= p < j && p in x.0 :: i>0 &&  v[i-1] + x.1 >= p
  ensures isSolution(x, v_modified) 
  ensures isBetterSol(x,v_modified,v)//they are equal
  ensures |v_modified| == |v|
  ensures v_modified[i] == j
  ensures v_modified[..i] == v[..i]
  {
    v_modified := v[i := j];
    changePos(x,v,i,j,i);
    assert forall m | m in x.0 :: covered(x,v_modified,m);

    var k := i+1;
    while (k<|v_modified| && v_modified[k]<j)
      invariant i < k <= |v_modified| == |v|
      invariant sorted(v_modified[..k])
      invariant forall m | m in x.0 :: covered(x,v_modified,m)
      invariant v_modified[..i] == v[..i]
      invariant forall m | i <= m < k :: v_modified[m] == j
      invariant v_modified[k..] == v[k..]
      decreases |v_modified|-k
      {
        changePos(x,v_modified,i,j,k);
        v_modified := v_modified[k := j];
        k := k+1;
      }

    assert sorted(v_modified);
    assert forall i | i in x.0 :: covered(x,v_modified,i);
    
    //assert isSolution(x,v_modified);
    //assert isBetterSol(x,v_modified,v);
  }

  lemma changePos(x:Input, sol:Solution, i:nat, j:nat, k:nat)
  requires isValidInput(x)
  requires 0 <= i <= k < |sol| && sol[k] < j 
  requires sorted(sol[..k])
  requires sorted(sol[k..])
  requires forall m | sol[i] <= m < j && m in x.0 ::  i > 0  && sol[i-1] <= m && sol[i-1] + x.1 >= m
  requires forall m | m < sol[i] && m in x.0 :: (exists z :: 0<=z < i && sol[z] <= m && sol[z]+x.1 >=m)
  requires forall m | m >= j && m in x.0 :: (exists z :: k <= z < |sol| && sol[z] <= m && sol[z]+x.1 >=m)
  requires forall m | m in x.0 :: covered(x,sol,m)
  ensures forall m | m in x.0 :: covered(x,sol[k := j],m)
  {
    forall m | m in x.0 
      ensures covered(x,sol[k := j],m)       
      {
        if (m < sol[i]) { 
          var z :| 0 <=z < i && sol[z] <= m && sol[z]+x.1 >=m;       
          assert  sol[z] == sol[k:=j][z];
          assert sol[z] in sol[k:=j];
          assert covered(x,sol[k := j],m);}
        else if (m >= j) { 
          var z :| k <= z < |sol| && sol[z] <= m && sol[z]+x.1 >=m;
          if (z==k) { 
            assert sol[k:=j][k] in sol[k:=j];
            assert covered(x,sol[k := j],m);
          }
          else {
            assert  sol[z] == sol[k:=j][z];
            assert sol[z] in sol[k:=j];
            assert covered(x,sol[k := j],m);
          }
        }
        else{
          assert sol[i-1]== sol[k:=j][i-1];
          assert sol[i-1] in sol[k:=j]; 
          assert sol[i-1] + x.1 >= m;
          assert sol[i-1] <= m;
          assert covered(x,sol[k := j],m);
        }
      }
  }
}
