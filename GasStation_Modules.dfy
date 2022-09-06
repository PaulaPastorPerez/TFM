include "ModulesValue.dfy"

module GasStation refines GreedyAlgorithmValue {
  type Input = (seq<nat>, nat)
  type Elem = bool

  class InputA ... {
    var distance: array<nat>;
    var k: nat;

    constructor (d:array<nat>,l:nat)
    {
      distance := d;
      k := l;
      Repr := {this,distance};
    }

    predicate Valid()
    {
      Repr == {this,this.distance}
    } 
  }

  class OutputA ... {
    var sol: array<Elem>;
    var stops: nat;
    var size: nat; //partial output

    constructor (x:InputA)
      requires x.Valid()
      ensures forall z | z in Repr :: fresh(z)
      ensures Valid(x)
    { 
      sol := new Elem[x.distance.Length+1];
      Repr := {this,sol};
      stops := 0;
      size := 0;
    }

    predicate Valid(x:InputA)
    {
      Repr == {this,sol} &&
      sol.Length == x.distance.Length+1 &&
      0 <= size <= sol.Length &&
      stops == value(inputTrans(x),sol[..size])
    }
  }

  //NEEDED FUNCTIONS

  predicate sorted(s:seq<int>) {
	  forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
  }

  function sum(a:seq<nat>, b:Solution):nat
  requires |a| == |b| >= 0
  {
    if (|a|== 0) then 0 
    else if b[|b|-1] then sum(a[..|a|-1], b[..|b|-1]) + a[|a|-1]
         else sum(a[..|a|-1], b[..|b|-1])
  }


  function value(x:Input, b:Solution):nat
  {
    if (|b|== 0) then 0
    else if b[|b|-1] then value(x, b[..|b|-1]) + 1
         else value(x, b[..|b|-1])
  }

  function sum_distance(a:seq<nat>):nat
  requires |a| >= 0
  {
    if (|a| == 0) then 0
    else sum_distance(a[..|a|-1]) + a[|a|-1]
  }

  //PREDICATES

  predicate smaller(x:Input) 
  {
	  forall m | 0 <= m < |x.0| :: (x.0)[m] <= x.1
  }

  function solutionValue(x: Input, s: Solution): nat
  {
    value(x,s)
  }

  predicate isValidInput(x:Input) {
    |x.0|>0 && smaller(x)
  }

  function inputTrans(x:InputA) : Input
  { 
    (x.distance[..],x.k)
  }

  function outputTrans(x:InputA,y:OutputA) : Solution
  { 
    (y.sol)[..]
  }

  //---------- 1. IS SOLUTION ----------

  predicate consecutive_stops(i:nat, j:nat, s:Solution)
  requires 0 <= i < j < |s|
  {
    s[i] == s[j] == true && forall k | i < k < j :: s[k] == false
  }

  predicate isPartialSolution(x:Input, s:Solution)
  requires isValidInput(x)
  requires |s| <= |x.0| + 1
  {
    forall i, j | 0 <= i < j <= |s|-1 && consecutive_stops(i,j,s) :: sum_distance(x.0[i..j]) <= x.1
  }

  predicate isSolution(x:Input, s:Solution)
  {
    |s| == |x.0|+1 && s[0] == s[|s|-1] == true && isPartialSolution(x,s)
  }

  //---------- 1.1. EXISTENCE OF SOLUTION ----------

  lemma existsSolution(x:Input)
  {
    var sol := seq(|x.0|+1, n => true);

    {solAllTrue(x,sol);}
    assert isSolution(x,sol);
  }

  lemma solAllTrue(x:Input, sol:Solution)
  requires isValidInput(x)
  requires |x.0|+1 == |sol| && forall i | 0 <= i < |sol| :: sol[i] == true
  ensures forall i,j | 0 <= i < j <= |sol|-1 && consecutive_stops(i,j,sol) :: sum_distance(x.0[i..j]) <= x.1
  {
    forall i,j | 0 <= i < j <= |sol|-1 && consecutive_stops(i,j,sol) ensures i+1 == j
    {
      if (i+1 != j) {
        assert sol[i+1] == true;
        assert !consecutive_stops(i,j,sol);
      }
      else {}
    }
  }

  //---------- 2. IS BETTER SOLUTION ----------

  predicate isBetterSol(x:Input, s1:Solution, s2:Solution)

  lemma isBetterSolTrans(x:Input, s1:Solution, s2:Solution, s3:Solution)

  lemma isBetterSolRefl(x:Input, s:Solution)

  //---------- 3. IS GREEDY SOLUTION ----------

  predicate isPartialSolGreedy(x:Input, s:Solution)
  requires isValidInput(x) && |s| < |x.0| + 1
  requires isPartialSolution(x, s)
  {
    forall i,j | 0 <= i < j <= |s|-1 && consecutive_stops(i,j,s) :: sum_distance(x.0[i..j+1]) > x.1
  }

  predicate isSolGreedy(x:Input, s:Solution)
  {
    |s| == |x.0|+1 && s[0]==s[|s|-1]==true && isPartialSolGreedy(x,s[..|s|-1])
  }

  //---------- 4. IS OPTIMAL SOLUTION ----------

  predicate isSolOptimal(x:Input, s:Solution)

  lemma betterThanOptimal(x:Input, s:Solution, optimalS:Solution)

  //---------- 5. ALGORITHM ----------

  method greedy(x:InputA) returns (res:OutputA)
  {
    var km := (x.distance)[0]; //kilometers walked since the last stop
    res := new OutputA(x);    
    res.sol[0] := true;
    res.stops := 1;
    res.size := 1; 

    var j := 0;

    while res.size < (x.distance).Length
      decreases (x.distance).Length - res.size
      invariant 0 <= res.size <= (x.distance).Length 
      invariant  0 <= j < res.size 
      invariant res.sol.Length==(x.distance).Length+1>0 && (res.sol)[0] == true
      //invariants for isPartialSolution
      invariant km == sum_distance((x.distance)[j..res.size]) <= x.k
      invariant (res.sol)[j] == true && forall z | j < z < res.size :: (res.sol)[z] == false
      //invariant for the postconditions
      invariant isPartialSolution(inputTrans(x),(res.sol)[..res.size])
      invariant isPartialSolGreedy(inputTrans(x),(res.sol)[..res.size])
      //To be able to fill the solution array
      invariant forall z | z in res.Repr :: fresh(z)
      invariant res.Valid(x)

      {
        if (km + (x.distance)[res.size] <= x.k) { //it does not stop
          (res.sol)[res.size] := false;
          km := km + (x.distance)[res.size];

          assert (x.distance)[j..res.size+1] == (x.distance)[j..res.size]+ [(x.distance)[res.size]]; //to restore km
          propertyRestoreF(inputTrans(x),(res.sol)[..res.size],j);
          propertyRestoreF_2(inputTrans(x),(res.sol)[..res.size],j);
          assert res.sol[..res.size+1]==res.sol[..res.size]+[false];
          assert value(inputTrans(x),res.sol[..res.size+1])==value(inputTrans(x),res.sol[..res.size]);
        }
        else { //it stops
          ghost var oldj:=j;
          propertyRestoreT(inputTrans(x),(res.sol)[..res.size],oldj);

          assert (x.distance)[j..res.size+1] == (x.distance)[j..res.size]+ [(x.distance)[res.size]]; //to restore km
          assert sum_distance((x.distance)[j..res.size+1]) > x.k;
          propertyRestoreT_2(inputTrans(x),(res.sol)[..res.size],oldj);

          assert (x.distance)[j..res.size+1] == (x.distance)[j..res.size]+ [(x.distance)[res.size]]; //to restore km
          assert sum_distance((x.distance)[j..res.size+1]) > x.k;
          assert forall z | z in res.Repr :: fresh(z);
          (res.sol)[res.size] := true;

          assert (res.sol)[..res.size+1] == (res.sol)[..res.size] + [(res.sol)[res.size]];
          assert isPartialSolution(inputTrans(x),(res.sol)[..res.size+1]);
          assert isPartialSolGreedy(inputTrans(x),(res.sol)[..res.size+1]);
          assert value(inputTrans(x),res.sol[..res.size+1])==1+value(inputTrans(x),res.sol[..res.size]);
          j := res.size;
          km := (x.distance)[j];
          res.stops := res.stops+1;
        }
        res.size := res.size+1;
      }

    (res.sol)[res.size] := true;
    res.stops:=res.stops+1;
    assert res.size == x.distance.Length;
    assert res.sol[..res.size+1]==res.sol[..];
    assert res.stops == value(inputTrans(x),res.sol[..res.size+1]);
    assert isPartialSolution(inputTrans(x),(res.sol)[..res.size]);
    assert isPartialSolGreedy(inputTrans(x),(res.sol)[..res.size]);

    res.size:=res.size+1;

    assert isSolution(inputTrans(x),(res.sol)[..]);
    assert isSolGreedy(inputTrans(x),(res.sol)[..]);
  }

  lemma propertyRestoreF(x:Input, sol:Solution, lastT:int)
  requires isValidInput(x) && |sol|<|x.0| 
  requires isPartialSolution(x,sol) 
  requires 0<=lastT<|sol| && sol[lastT]==true && forall z | lastT < z < |sol| :: sol[z]==false
  requires sum_distance(x.0[lastT..|sol|+1]) <= x.1
  ensures isPartialSolution(x,sol+[false])
  {
    assert |sol+[false]|==|sol|+1;
    forall c,f | 0 <= c < f < |sol|+1 && consecutive_stops(c,f,sol+[false])
    ensures sum_distance(x.0[c..f]) <= x.1;
    {
      if (f < |sol|) { 
        assert forall z | 0<=z<|sol| :: (sol+[false])[z]==sol[z];
        assert consecutive_stops(c,f,sol);
        assert sum_distance(x.0[c..f]) <= x.1;
      }
      else {
        assert !consecutive_stops(c,|sol|,sol+[false]);}
      }
  }

  lemma propertyRestoreT(x:Input, sol:Solution, lastT:int)
  requires isValidInput(x) && |sol|<=|x.0|
  requires isPartialSolution(x,sol)
  requires 0<=lastT<|sol| && sol[lastT]==true && forall z | lastT < z < |sol| :: sol[z]==false
  requires sum_distance(x.0[lastT..|sol|]) <= x.1
  ensures isPartialSolution(x,sol+[true])
  {
    assert |sol+[true]|==|sol|+1;
    forall c,f | 0 <= c < f < |sol|+1 && consecutive_stops(c,f,sol+[true]) 
      ensures sum_distance(x.0[c..f]) <= x.1
      {
        if (f < |sol|){ 
          assert forall z | 0<=z<|sol| :: (sol+[true])[z]==sol[z];
          assert consecutive_stops(c,f,sol);
        }
        else {         
          assert consecutive_stops(lastT,|sol|,sol+[true]);
        }
      }
  }

  lemma propertyRestoreF_2(x:Input, sol:Solution, lastT:int)
  requires isValidInput(x) && |sol|<|x.0|
  requires isPartialSolution(x,sol) && isPartialSolution(x,sol+[false])
  requires isPartialSolGreedy(x,sol)
  requires 0<=lastT<|sol| && sol[lastT]==true && forall z | lastT < z < |sol| :: sol[z]==false
  requires sum_distance(x.0[lastT..|sol|+1]) <= x.1
  ensures isPartialSolGreedy(x,sol+[false])
  {
    assert |sol+[false]|==|sol|+1;
    forall c,f | 0 <= c < f <= |sol| && consecutive_stops(c,f,sol+[false])
      ensures sum_distance(x.0[c..f+1]) > x.1;
      {
        if (f < |sol|) { 
          assert forall z | 0<=z<|sol|-1 :: (sol+[false])[z]==sol[z];
          assert consecutive_stops(c,f,sol);
          assert sum_distance(x.0[c..f+1]) > x.1;
        }
        else {
          assert !consecutive_stops(c,|sol|,sol+[false]);
        }
      }
  }

  lemma propertyRestoreT_2(x:Input, sol:Solution, lastT:int)
  requires isValidInput(x) && |sol|<|x.0|
  requires isPartialSolution(x,sol) && isPartialSolution(x,sol+[true])
  requires isPartialSolGreedy(x,sol) 
  requires 0<=lastT<|sol| && sol[lastT]==true && forall z | lastT < z < |sol| :: sol[z]==false
  requires sum_distance(x.0[lastT..|sol|]) <= x.1
  requires sum_distance(x.0[lastT..|sol|+1]) > x.1
  //it is needed to add a precondition to ensure the sum of one more gas station is not possible
  ensures isPartialSolGreedy(x,sol+[true])
  {
    assert |sol+[true]|==|sol|+1;
    forall c,f | 0 <= c < f <= |sol| && consecutive_stops(c,f,sol+[true]) 
      ensures sum_distance(x.0[c..f+1]) > x.1
      {
        if (f < |sol|){ 
          assert forall z | 0<=z<|sol|-1 :: (sol+[true])[z]==sol[z];
          assert consecutive_stops(c,f,sol);
          assert sum_distance(x.0[c..f+1]) > x.1;
        }
        else {     
          assert consecutive_stops(lastT,|sol|,sol+[true]);
        }
      }
  }

  //---------- 6. VERIFICATION ----------

  ghost method endReduction(x:Input, greedy:Solution, optimal:Solution) returns (optimal':Solution)
  {
    optimal' := optimal;
    assert optimal'[0..|greedy|] == optimal' && greedy[0..|greedy|] == greedy;
    assert value(x,optimal') <= value(x,greedy);
    assert isBetterSol(x,greedy,optimal);
  }

  ghost method reduction_step(x:Input, greedy:Solution, optimal:Solution, i:nat) returns (optimal':Solution)
  {
    if (greedy[i]==true) //&& optimal[i]==false
    {//Impossible

      //We are not allowing i to be 0 to make sure the existence of a previous TRUE.
      existTrueB(x,optimal,i);
      var lastT :| 0 <= lastT < i && optimal[lastT] == true && forall n | lastT < n < i :: optimal[n] == false;
      existTrueA(x,optimal,i);
      var nextT :| i <= nextT < |optimal| && optimal[nextT] == true && forall n | i < n < nextT :: optimal[n] == false;

      //Prove that as (lastT,i) are consecutive stops and the distance is  <= k, then (lastT,i+1) has distance > k. 
      //So, (lastT,nextT) are consecutive stops with distance >k. So, it is not sol.
      assert consecutive_stops(lastT,i,greedy) && sum_distance(x.0[lastT..i]) <= x.1;
      assert isPartialSolGreedy(x,greedy[..|greedy|-1]) ==>
        (consecutive_stops(lastT,i,greedy[..|greedy|-1]) ==> sum_distance(x.0[lastT..i+1]) > x.1);
      sumConm(x.0,i+1,nextT,lastT);
      //assert sum_distance(distance[lastT..nextT]) == sum_distance(distance[lastT..i+1]) + sum_distance(distance[i+1..nextT]);
      assert x.1 < sum_distance(x.0[lastT..i+1]) <= sum_distance(x.0[lastT..nextT]);

      assert !isPartialSolution(x,optimal);
      assert !isSolution(x,optimal);
    }
    else //greedy[i] == false && optimal[i] == true
    { 
      existTrueB(x,optimal,i);
      var lastT :| 0 <= lastT < i && optimal[lastT] == true && forall n | lastT < n < i :: optimal[n] == false;
      assert greedy[lastT] == true && forall n | lastT < n < i :: greedy[n] == false;

      existTrueA(x,greedy,i);
      var nextT :| i < nextT < |greedy| && greedy[nextT] == true && forall n | i < n < nextT :: greedy[n] == false;
     
      sumConm(x.0,i+1,nextT,lastT);
      //assert sum_distance(distance[lastT..nextT]) == sum_distance(distance[lastT..i+1]) + sum_distance(distance[i+1..nextT]);
      assert sum_distance(x.0[lastT..i+1]) <= sum_distance(x.0[lastT..nextT]) <= x.1;
      optimal' := postpone(x,optimal,i,lastT);
    }
  }

  //Exist a TRUE to the left of i
  lemma existTrueB(x:Input, sol:Solution, i:nat)
  requires isValidInput(x)
  requires isSolution(x,sol)
  requires 0 < i <= |sol|
  ensures exists j :: 0 <= j < i && sol[j] == true && forall n | j < n < i :: sol[n] == false
  {
    if (sol[i-1] == true) {}
    else { 
      if (i-1) == 0 {
        assert sol[i-1] == true;
      }
      else {
        existTrueB(x,sol,i-1);
      }
    }
  }

  //Exist a TRUE to the right of i
  lemma existTrueA(x:Input, sol:Solution, i:nat)
  decreases |sol|-i
  requires isValidInput(x)
  requires isSolution(x,sol)
  requires 0 <= i < |sol|-1 && sol[i] == false
  ensures exists j :: i < j < |sol| && sol[j] == true && forall n | i < n < j :: sol[n] == false
  {
    if (sol[i+1] == true) {}
    else { 
      if (i+1) == |sol|-1 {
        assert sol[i-1] == true;
      }
      else {
        existTrueA(x,sol,i+1);
      }
    }
  }

  //---------- 7. POSTPONE LEMMA ----------

  lemma sumConm(a:seq<nat>,i:nat,j:nat,m:nat)
  requires 0 <= m < i <= j < |a|+1
  ensures sum_distance(a[m..j]) == sum_distance(a[m..i]) + sum_distance(a[i..j])
  { 
    if (i < j) { calc == {
      sum_distance(a[m..j]);
      {assert a[m..j] == a[m..j-1] + [a[j-1]];}
      sum_distance(a[m..j-1]) + a[j-1];
      {sumConm(a,i,j-1,m);}
      sum_distance(a[m..i]) + sum_distance(a[i..j-1]) + a[j-1];
      {assert a[i..j-1] + [a[j-1]] == a[i..j]; }
      sum_distance(a[m..i]) + sum_distance(a[i..j]);
    }}
    else { calc == {
      sum_distance(a[m..j]);
      {assert sum_distance(a[i..j]) == 0;}
      sum_distance(a[m..i]);
    }}
  }

  lemma valueMore(a:Input,b:Solution,i:nat)
  requires 0 <= i < |b|
  requires b[i]==false
  ensures value(a,b[i:=true]) == value(a,b) + 1 
  {}

  lemma valueLess(a:Input,b:Solution,i:nat)
  requires 0 <= i < |b|
  requires b[i]==true
  ensures value(a,b[i:=false]) == value(a,b) - 1
  {}

  lemma valueSame(a:Input,b:Solution,i:nat)
  requires 0 <= i < |b|
  //requires b[i] == true
  ensures value(a,b[i:=b[i]]) == value(a,b)
  {}

  lemma lessStops(a:Input,b:Solution,i:nat,j: nat)
  requires 0 <= i < j < |b|==|a.0|+1
  requires b[i] == true // Similarly the other way around
  ensures value(a,b) >= value(a,b[i:=false][j:=true])
  { if (b[j] == true) {calc =={
      value(a,b[i:=false][j:=true]);
      {valueSame(a,b[i:=false],j);}
      value(a,b[i:=false]);
      {valueLess(a,b,i);}
      value(a,b) - 1;
      <= value(a,b);
    }}
    else { calc == {
      value(a,b[i:=false][j:=true]);
      {valueMore(a,b[i:=false],j);}
      value(a,b[i:=false]) + 1;
      {valueLess(a,b,i);}
      value(a,b) - 1 + 1;
      value(a,b);
    }}
  }

  //We must change v[i] from TRUE to FALSE, v[j] from FALSE to TRUE, and all n's between i and j to FALSE.
  ghost method postpone(x:Input, v:Solution, i: nat, lastT:nat) returns (v_modified:Solution) 
  requires isValidInput(x)
  requires isSolution(x, v)
  requires 0 <= lastT < i < |v|-1 //i and j can not be 0 either |v|-1
  requires v[i] == true && v[lastT] == true
  requires sum_distance(x.0[lastT..i+1]) <= x.1
  requires consecutive_stops(lastT,i,v)
  ensures isSolution(x, v_modified)
  ensures isBetterSol(x, v_modified, v) //they are equal
  ensures v_modified == v[i := false][i+1 := true]
  { 
    //Postpone the stop -> we made the needed change in v_modified
    v_modified := v[i:=false][i+1:=true];

    assert v_modified[0..i] == v[0..i] && v_modified[i+2..|v|] == v[i+2..|v|];
    isSol(x,v,v_modified,i,lastT);

    //isBetterSol(distance,k,v_modified,v)
    lessStops(x,v,i,i+1);
    assert isBetterSol(x,v_modified,v);
  }

  lemma isSol(x:Input, v:Solution, v_modified:Solution, i:nat, lastT:nat)
  requires isValidInput(x)
  requires 0 <= lastT < i < |v|-1
  requires consecutive_stops(lastT,i,v)
  requires isSolution(x,v)
  requires sum_distance(x.0[lastT..i+1]) <= x.1 
  requires v_modified == v[i:=false][i+1:=true]
  ensures isSolution(x,v_modified)
  {
    assert |v| == |v_modified|;
    forall c,f | 0 <= c < f < |v| && consecutive_stops(c,f,v_modified)
      ensures sum_distance(x.0[c..f]) <= x.1;
      {
        assert forall z | 0 <= z < i || i+1 < z < |v| :: v_modified[z] == v[z];
        if ((f < i) || (i+1 < c) || (c==i+1 && v[i+1]==true)) { 
          assert consecutive_stops(c,f,v);
          assert sum_distance(x.0[c..f]) <= x.1;
        }
        else {
          assert v_modified[i+1]==true;
          assert c==i+1 || f==i+1;
          if (c == i+1) { 
            sumConm(x.0,i+1,f,i);
            assert sum_distance(x.0[i+1..f]) <= sum_distance(x.0[i..f])<=x.1;}
          else {}
        } 
      }
  }
}