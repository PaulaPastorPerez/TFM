include "ModulesValue.dfy"

module Files refines GreedyAlgorithmValue {
  type Input = (seq<nat>, nat)
  type Elem = bool

  class InputA ... {
    var s_files: array<nat>;
    var s_disc: nat;

    constructor (f:array<nat>,d:nat)
    ensures Valid()
    ensures s_files == f && s_disc == d
    {
      s_files := f;
      s_disc := d;
      Repr := {this,s_files};
    }
    
    predicate Valid()
    {
      Repr == {this, this.s_files}
    }
  }

  class OutputA ... {
    var sol: array<Elem>;
    var files: nat;
    var size: nat; //partial output

    constructor (x:InputA)
      requires x.Valid()
      ensures forall z | z in Repr :: fresh(z)
      ensures Valid(x)
      ensures sol.Length == x.s_files.Length
      ensures size == 0
    {
      sol := new Elem[x.s_files.Length];
      Repr := {this,sol};
      files := 0;
      size := 0;
    }

    predicate Valid(x:InputA)
    {
      Repr == {this, sol} &&
      sol.Length == x.s_files.Length &&
      0 <= size <= sol.Length &&
      files == value(inputTrans(x),sol[..size])
    }
  }

  //NEEDED FUNCTIONS

  predicate sorted(s : seq<int>) {
	  forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
  }

  function sum(a:seq<nat>, b:Solution) : nat
  requires |a| == |b| >= 0
  {
    if (|a|== 0) then 0 
    else if b[|b|-1] then sum(a[..|a|-1], b[..|b|-1]) + a[|a|-1]
         else sum(a[..|a|-1], b[..|b|-1])
  }

  function value(a:Input, b:Solution) : nat
  ensures 0 <= value(a,b) <= |b|
  {
    if (|b|== 0) then 0 
      else if b[|b|-1] then value(a, b[..|b|-1]) + 1
         else value(a, b[..|b|-1])
  }

  //PREDICATES

  function solutionValue(x: Input, s: Solution): nat
  {
    |x.0| - value(x,s)
  }

  predicate isValidInput(x: Input) {
    sorted(x.0)
  }

  function inputTrans(x:InputA) : Input
  {
    (x.s_files[..],x.s_disc)
  }

  method inputRecover(x: Input) returns (s: InputA)
  {
    var i := 0;
    var a := new nat[|x.0|];
    while i < |x.0|
      invariant 0 <= i <= |x.0|
      invariant forall j | 0 <= j < i :: a[j] == x.0[j]
    {
      a[i] := x.0[i];
      i := i + 1;
    }
    assert forall j | 0 <= j < |x.0| :: a[j] == x.0[j];
    assert a[..] == x.0;
    s := new InputA(a, x.1);
    assert inputTrans(s) == (a[..], x.1);
    assert inputTrans(s) == x;
  }

  function outputTrans(x:InputA,y:OutputA) : Solution
  {
    (y.sol)[..]
  }

  method outputRecover(xA: InputA, y: Solution) returns (s: OutputA)
  {
    assert isValidInput(inputTrans(xA));
    assert isSolution(inputTrans(xA), y);
    assert |y| == |inputTrans(xA).0|;

    s := new OutputA(xA);
    assert s.sol.Length == |y|;
    assert s.Valid(xA);    
    var i := 0;
    while i < |y|
     modifies s`files, s`size, s.sol
      invariant 0 <= i <= |y| && i == s.size
      invariant s.sol.Length == |y|
      invariant forall j | 0 <= j < i :: s.sol[j] == y[j]
      invariant s.Valid(xA)
     

      invariant s.files == value(inputTrans(xA),s.sol[..s.size])
    { 
      assert (s.sol)[..s.size + 1][..s.size] == (s.sol)[..s.size];

      s.sol[i] := y[i];
      if (y[i] == true) {
        s.files := s.files+1;}
      s.size := s.size + 1;
      i := i + 1;
    }
    assert outputTrans(xA, s) == y;
  }

  //---------- 1. IS SOLUTION ----------

  predicate isSolution(x:Input, s:Solution)
  {
    |s| == |x.0| && sum(x.0, s) <= x.1
  }

  //---------- 1.1. EXISTENCE OF SOLUTION ----------

  lemma existsSolution(x:Input)
  {
    var sol := seq(|x.0|, n => false);

    {sumAllFalse(x.0,sol);}
    assert sum(x.0,sol) == 0;
    assert isSolution(x,sol);
  }

  lemma sumAllFalse(a:seq<nat>, b:Solution)
  requires |a| == |b| && forall i | 0 <= i < |b| :: b[i] == false
  ensures sum(a,b) == 0
  decreases |b|
  {
    if |a| == 0 {}
    else {
      assert sum(a,b) == sum(a[..|a|-1],b[..|b|-1]) + (if b[|b|-1] then a[|a|-1] else 0);
      {sumAllFalse(a[..|a|-1],b[..|b|-1]);}
    }
  }

  //---------- 2. IS BETTER SOLUTION ----------

  predicate isBetterSol(x:Input, s1:Solution, s2:Solution)

  lemma isBetterSolTrans(x:Input, s1:Solution, s2:Solution, s3:Solution)

  lemma isBetterSolRefl(x:Input, s:Solution)

  //---------- 3. IS GREEDY SOLUTION ----------

  predicate isSolGreedy(x:Input, s:Solution)
  {
    (forall i,j | 0<=i<j<|s| :: (s[i] == false ==> s[j] == false)) && 
    forall m | 0<=m<|s| && s[m] == false :: (sum(x.0, s[m := true]) > x.1)
  }

  //---------- 4. IS OPTIMAL SOLUTION ----------

  predicate isSolOptimal(x:Input, s:Solution)

  lemma betterThanOptimal(x:Input, s:Solution, optimalS:Solution)

  //---------- 5. ALGORITHM ----------

  method greedy(x:InputA) returns (res:OutputA)
  {
    var accum := 0;
    res := new OutputA(x);
    res.files := 0;
    res.size := 0;

    while (res.size < x.s_files.Length && (accum + (x.s_files)[res.size] <= x.s_disc))
      decreases (x.s_files).Length - res.size
      invariant 0 <= res.size <= (x.s_files).Length == (res.sol).Length
      invariant accum <= x.s_disc
      invariant accum == sum((x.s_files)[..res.size], (res.sol)[..res.size])
      invariant isSolution((x.s_files[..res.size],x.s_disc), (res.sol)[..res.size])
      invariant isSolGreedy((x.s_files[..res.size],x.s_disc), (res.sol)[..res.size])
      //To be able to fill the solution array
      invariant forall z | z in res.Repr :: fresh(z)
      invariant res.Valid(x)
      {
        res.sol[res.size] := true;
        accum := accum + (x.s_files)[res.size]; 

        assert (x.s_files)[..res.size + 1][..res.size] == (x.s_files)[..res.size];
        assert (res.sol)[..res.size + 1][..res.size] == (res.sol)[..res.size];
        
        res.files := res.files + 1;
        res.size := res.size + 1;
      }

    while (res.size < (x.s_files).Length)
      decreases (x.s_files).Length - res.size
      invariant 0 <= res.size <= (x.s_files).Length == (res.sol).Length
      invariant accum == sum((x.s_files)[..res.size], (res.sol)[..res.size]) 
      invariant isSolGreedy((x.s_files[..res.size],x.s_disc), (res.sol)[..res.size])
      //To be able to fill the solution array
      invariant forall z | z in res.Repr :: fresh(z)
      invariant res.Valid(x)
      {
        (res.sol)[res.size] := false;

        assert (x.s_files)[..res.size + 1][..res.size] == (x.s_files)[..res.size];
        assert (res.sol)[..res.size + 1][..res.size] == (res.sol)[..res.size];

        res.size := res.size + 1;
      }

    assert (x.s_files)[..] == (x.s_files)[..(x.s_files).Length];
    assert (res.sol)[..] == (res.sol)[..(x.s_files).Length];
  }

  //---------- 6. VERIFICATION ----------

  ghost method endReduction(x:Input, greedy:Solution, optimal:Solution) returns (optimal':Solution)
  {
    optimal' := optimal;
  }

  ghost method reduction_step(x:Input, greedy:Solution, optimal:Solution, i:nat) returns (optimal':Solution)
  {
    if (greedy[i] == false) //&& optimal[i]==true
    { //Impossible

      {sumFalse(x.0, greedy, i);}
      assert sum(x.0, greedy[i := true]) == sum(x.0[..i+1], greedy[i := true][..i+1]);
      assert greedy[i:=true][..i+1] == optimal[..i+1];
      assert sum(x.0[..i+1], greedy[i := true][..i+1]) == sum(x.0[..i+1], optimal[..i+1]);
      {sumSmaller(x.0, optimal, i);}
      assert sum(x.0[..i+1], optimal[..i+1]) <= sum(x.0, optimal) <= x.1;

      assert sum(x.0, greedy[i := true]) <= x.1;
      assert !isSolGreedy(x, greedy);
    }
    else
    { {existTrue(x, greedy, optimal, i); }
      //assert exists j :: i < j < |optimal| && optimal[j] == true;
      var j :| i < j < |optimal| && optimal[j] == true;
      optimal' := swap(x, optimal, i, j);
    }
  }

  lemma sumFalse(a:seq<nat>, b:Solution, i:nat)
  requires 0 <= i < |a| == |b|
  requires b[i] == false && forall j | i < j < |b| :: b[j] == false
  ensures sum(a, b[i := true]) == sum(a[..i+1], b[i := true][..i+1])
  {
    if (i < |b|-1) { calc {
      sum(a,b[i:=true]);
      sum(a[..|a|-1], b[..|b|-1][i:=true]) + (if b[|b|-1] then a[|a|-1] else 0);
      {assert b[|b|-1] == false; }
      sum(a[..|a|-1], b[..|b|-1][i:=true]);
      {sumFalse(a[..|a|-1], b[..|b|-1], i); }
      sum(a[..|a|-1][..i+1], b[..|b|-1][i := true][..i+1]);
      {assert a[..|a|-1][..i+1] == a[..i+1] && b[..|b|-1][i := true][..i+1] == b[i := true][..i+1]; }
      sum(a[..i+1], b[i := true][..i+1]);
    }}
    else { calc {
      sum(a,b[i:=true]);
      {assert a == a[..i+1] == a[..|a|]; }
      {assert b[i:=true] == b[i:=true][..i+1] == b[i:=true][..|b|]; }
      sum(a[..i+1], b[i := true][..i+1]);
    }}
  }

  lemma sumSmaller(a:seq<nat>, b:Solution, i:nat)
  requires sorted(a)
  requires 0 <= i < |a| == |b|
  ensures sum(a[..i+1], b[..i+1]) <= sum(a, b)
  {
    if (i == |a|-1) {calc {
      sum(a[..i+1], b[..i+1]);
      sum(a[..|a|], b[..|b|]);
      {assert a[..|a|] == a && b[..|b|] == b;}
      sum(a,b);
    }}
    else {calc >= {
      sum(a,b);
      sum(a[..|a|-1], b[..|b|-1]) + (if b[|b|-1] then a[|a|-1] else 0);
      {sumSmaller(a[..|a|-1], b[..|b|-1], i);}
      sum(a[..|a|-1][..i+1], b[..|b|-1][..i+1]);
      {assert a[..|a|-1][..i+1] == a[..i+1] && b[..|b|-1][..i+1] == b[..i+1]; }
      sum(a[..i+1], b[..i+1]);
    }}
  }

  lemma existTrue(x:Input, greedy:Solution, optimal:Solution, i:nat)
  requires sorted((x.0)[..])
  requires isSolution(x, greedy) && isSolution(x, optimal)
  requires isSolGreedy(x, greedy) && isSolOptimal(x, optimal)
  requires 0 <= i < |optimal|==|greedy|
  requires greedy[0..i] == optimal[0..i]
  requires optimal[i] == false && greedy[i] == true
  ensures exists j :: i < j < |optimal| && optimal[j] == true
  {
    if (forall j | i < j < |optimal| :: optimal[j] == false) { 
      falseValue(x,optimal,i);
      assert greedy[..i+1][..|greedy[..i+1]|-1] == greedy[..i];
      assert value(x,greedy[..i+1]) == 1 + value(x,greedy[..i]);
      monotone(x,greedy,i+1);
      assert value(x,optimal) == value(x,optimal[..i]) == value(x,greedy[0..i]) < value(x,greedy[..i+1]);
      assert !isSolOptimal(x, optimal);}
  }

  lemma monotone(x:Input,b:Solution,i:nat)
  requires 0 <= i <= |b|
  ensures value(x,b[..i]) <= value(x,b)
  {
    if (i == |b|) {
      assert b == b[..i];
    }
    else { calc >= {
      value(x,b);
      value(x,b[..|b|-1]) + (if b[|b|-1] then 1 else 0);
      value(x,b[..|b|-1]);
      //{monotone(a,b[..|b|-1],i);}
      value(x,b[..|b|-1][..i]);
      {assert b[..|b|-1][..i] == b[..i];}
      value(x,b[..i]);
    }}
  }

  lemma falseValue(x:Input,b:Solution,i:nat)
  requires 0 <= i <= |b|
  requires forall k | i <= k < |b| :: b[k]==false
  ensures value(x,b) == value(x,b[..i])
  {
    if (i == |b|) {
      assert b == b[..i];
    }
    else { calc {
      value(x,b);
      value(x,b[..|b|-1]) + (if b[|b|-1] then 1 else 0);
      value(x,b[..|b|-1]);
      //{falseValue(a,b[..|b|-1]);}
      {assert b[..|b|-1][..i] == b[..i];}
      value(x,b[..i]);
    }}
  }

  //---------- 7. SWAP LEMMA ----------

  lemma sumMore(a:seq<nat>,b:Solution,i:nat)
  requires 0 <= i < |a| == |b|
  requires b[i]==false
  ensures sum(a,b[i:=true]) == sum(a,b) + a[i] 
  {}

  lemma sumLess(a:seq<nat>,b:Solution,i:nat)
  requires 0 <= i < |a| == |b|
  requires b[i] == true
  ensures sum(a,b[i:=false]) == sum(a,b) - a[i] 
  {}

  lemma smallerSum(a:seq<nat>,b:Solution,i:nat,j: nat)
  requires sorted(a)
  requires 0 <= i < j < |b| == |a|
  requires b[i] == false && b[j] == true
  ensures sum(a,b) >= sum(a,b[i:=true][j:=false])
  { calc <={
    sum(a,b[i:=true][j:=false]);
    {sumLess(a,b[i:=true],j);}
    sum(a,b[i:=true])-a[j];
    {sumMore(a,b,i);}
    sum(a,b)+a[i]-a[j];
    {assert a[i] <= a[j];}
    sum(a,b);
    }
  }

  lemma valueMore(x:Input,b:Solution,i:nat)
  requires 0 <= i < |b|
  requires b[i] == false
  ensures value(x,b[i:=true]) == value(x,b) + 1 
  {}

  lemma valueLess(x:Input,b:Solution,i:nat)
  requires 0 <= i < |b|
  requires b[i] == true
  ensures value(x,b[i:=false]) == value(x,b) - 1
  {}

  lemma sameValue(x:Input,b:Solution,i:nat,j: nat)
  requires sorted(x.0)
  requires 0 <= i < j < |b| == |x.0|
  requires b[i] == false && b[j] == true // Similarly the other way around
  ensures value(x,b) == value(x,b[i:=true][j:=false])
  { calc =={
    value(x,b[i:=true][j:=false]);
    {valueLess(x,b[i:=true],j);}
    value(x,b[i:=true]) - 1;
    {valueMore(x,b,i);}
    value(x,b) + 1 - 1;
    value(x,b);
    }
  }

  ghost method swap(x:Input, v:Solution, i: nat, j: nat) returns (v_modified:Solution) 
  requires sorted(x.0)
  requires isSolution(x, v)
  requires 0 <= i < j < |v|
  requires v[i] == false && v[j] == true
  ensures isSolution(x, v_modified) 
  ensures isBetterSol(x,v_modified,v)//they are equal
  ensures v_modified == v[i := true][j := false]
  {
    v_modified := v[i := true][j := false];
    //They have the same value
    sameValue(x,v,i,j);
    assert value(x,v_modified) == value(x,v);
  
    //They take up less space because t_ficheros[i] <= t_ficheros[j]
    smallerSum(x.0,v,i,j);
    assert sum(x.0, v_modified) <= sum(x.0,v) <= x.1;
  }
}