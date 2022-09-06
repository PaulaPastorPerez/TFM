//MAXIMIZE THE NUMBER OF FILES IN A DISC

predicate sorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

//Functions

function sum(a:seq<nat>, b:seq<bool>):nat
requires |a| == |b| >= 0
{
    if (|a| == 0) then 0 
    else if b[|b|-1] then sum(a[..|a|-1], b[..|b|-1]) + a[|a|-1]
         else sum(a[..|a|-1], b[..|b|-1])
}

function value(sol:seq<bool>):nat
requires |sol| >= 0
{
 if (|sol| == 0) then 0 
    else if sol[|sol|-1] then value(sol[..|sol|-1]) + 1
         else value(sol[..|sol|-1])
}

//---------- 1. IS SOLUTION ----------

//Given a vector with the size of the files (sorted from the smallest to the biggest),
//the size of the disc and a solution. To be a solution it has to secure that the sum
//of all the files that we choose is smaller or equal to the size of the disc. 

predicate isSolution(s_files:seq<nat>, s_disc:nat, sol:seq<bool>)
requires sorted(s_files)
{
    |sol| == |s_files| && sum(s_files, sol) <= s_disc
}

//---------- 2. IS BETTER SOLUTION ----------

//Given two solutions possibles of the problem, for one solution to be the best one it
//has to verify that the sume of the files we choose is greater than the sum of the files
//we choose for the other solution.

predicate isBetterSol(s_files:seq<nat>, s_disc: nat, betterSol:seq<bool>, sol:seq<bool>)
requires sorted(s_files)
requires isSolution(s_files, s_disc, sol)
requires isSolution(s_files, s_disc, betterSol)
{
  value(sol) <= value(betterSol)
}

//---------- 3. IS GREEDY SOLUTION ----------

predicate isSolGreedy(s_files:seq<nat>, s_disc:nat, sol:seq<bool>)
requires sorted(s_files)
requires isSolution(s_files, s_disc, sol)
{
    (forall i,j | 0<=i<j<|sol| :: (sol[i] == false ==> sol[j] == false)) && 
    forall m | 0<=m<|sol| && sol[m] == false :: (sum(s_files, sol[m := true]) > s_disc)
}


//---------- 4. IS OPTIMAL SOLUTION ----------

predicate isSolOptimal(s_files:seq<nat>, s_disc:nat, optimalSol:seq<bool>)
requires sorted(s_files)
requires isSolution(s_files, s_disc, optimalSol)
{
    forall sol | isSolution(s_files,s_disc,sol) :: isBetterSol(s_files,s_disc,optimalSol,sol)
}

lemma betterThanOptimal(s_files:seq<nat>, s_disc:nat, sol:seq<bool>, optimalSol:seq<bool>)
requires sorted(s_files)
requires isSolution(s_files, s_disc, sol) 
requires isSolution(s_files, s_disc, optimalSol) && isSolOptimal(s_files, s_disc, optimalSol)
requires isBetterSol(s_files,s_disc,sol,optimalSol)
ensures isSolOptimal(s_files,s_disc,sol)
{}

//---------- 5. ALGORITHM ----------

method file_in_disc(s_files:array<nat>, s_disc:nat) returns (sol:array<bool>)
requires sorted(s_files[..])
ensures sol.Length == s_files.Length
ensures isSolution(s_files[..], s_disc, sol[..])
ensures isSolGreedy(s_files[..], s_disc, sol[..])
{
    var accum := 0;
    var i := 0;
    sol := new bool[s_files.Length];

    while (i < s_files.Length && (accum + s_files[i] <= s_disc))
      decreases s_files.Length - i
      invariant 0 <= i <= s_files.Length
      invariant accum <= s_disc
      invariant accum == sum(s_files[..i], sol[..i])
      invariant isSolution(s_files[..i], s_disc, sol[..i])
      invariant isSolGreedy(s_files[..i], s_disc, sol[..i])
      {
        sol[i] := true;
 
        accum := accum + s_files[i]; 

        assert s_files[..i + 1][..i] == s_files[..i];
        assert sol[..i + 1][..i] == sol[..i];
        
        i:= i+1;
      }


    while (i < s_files.Length)
      decreases s_files.Length - i
      invariant 0 <= i <= s_files.Length
      invariant accum == sum(s_files[..i], sol[..i]) 
      invariant isSolGreedy(s_files[..i], s_disc, sol[..i])
      {
        sol[i] := false;
        
        assert s_files[..i + 1][..i] == s_files[..i];
        assert sol[..i + 1][..i] == sol[..i];

        i := i + 1;
      }
    assert s_files[..] == s_files[..s_files.Length];
    assert sol[..] == sol[..s_files.Length];

}

//---------- 6. REDUCCIÓN DE DIFERENCIAS ----------

ghost method reduction(s_files:seq<nat>, s_disc:nat, greedy:seq<bool>, optimal:seq<bool>) 
requires sorted(s_files)
requires isSolution(s_files, s_disc, greedy)
requires isSolution(s_files, s_disc, optimal)
requires isSolGreedy(s_files, s_disc, greedy)
requires isSolOptimal(s_files, s_disc, optimal)
ensures isSolOptimal(s_files,s_disc,greedy)
{
    var i := 0; var optimal' := optimal;
    while (i < |greedy|)
     invariant 0 <= i <= |greedy|
     invariant isSolution(s_files, s_disc, optimal')
     invariant isBetterSol(s_files, s_disc, optimal', optimal)
     invariant optimal'[..i] == greedy[..i]
    {
        if (greedy[i] != optimal'[i])
        {
          optimal' := reduction_step(s_files, s_disc, greedy, optimal', i);
        }
        i := i + 1;

    }

   endReduction(s_files,s_disc,greedy,optimal,optimal');
   betterThanOptimal(s_files, s_disc, greedy, optimal);
}

lemma endReduction(s_files:seq<nat>, s_disc:nat, greedy:seq<bool>, optimal:seq<bool>, optimal':seq<bool>)
requires sorted(s_files)
requires isSolution(s_files,s_disc,greedy) && isSolution(s_files,s_disc,optimal) && isSolution(s_files,s_disc,optimal')
requires isSolGreedy(s_files,s_disc,greedy) && isSolOptimal(s_files,s_disc,optimal) && isSolOptimal(s_files,s_disc,optimal')
requires isBetterSol(s_files,s_disc,optimal',optimal)
requires optimal'[..|optimal|] == greedy[..|optimal|]
ensures optimal' == greedy
{}

ghost method reduction_step(s_files:seq<nat>, s_disc:nat, greedy:seq<bool>, optimal:seq<bool>, i:nat) returns (optimal':seq<bool>)
requires sorted(s_files[..])
requires isSolution(s_files, s_disc, greedy) && isSolution(s_files, s_disc, optimal)
requires isSolGreedy(s_files, s_disc, greedy) && isSolOptimal(s_files, s_disc, optimal)
requires 0 <= i < |greedy|
requires greedy[i] != optimal[i] && greedy[0..i] == optimal[0..i]
ensures isSolution(s_files, s_disc, optimal')
ensures isSolOptimal(s_files, s_disc, optimal') 
ensures isBetterSol(s_files, s_disc, optimal', optimal)
ensures |optimal| == |optimal'|
ensures optimal'[0..i+1] == greedy[0..i+1]
{
  if (greedy[i]==false) //&& optima[i]==true
   {//Impossible

    {sumFalse(s_files, greedy, i);}
    assert sum(s_files, greedy[i := true]) == sum(s_files[..i+1], greedy[i := true][..i+1]);
    assert greedy[i:=true][..i+1] == optimal[..i+1];
    assert sum(s_files[..i+1], greedy[i := true][..i+1]) == sum(s_files[..i+1], optimal[..i+1]);
    {sumSmaller(s_files, optimal, i);}
    assert sum(s_files[..i+1], optimal[..i+1]) <= sum(s_files, optimal) <= s_disc;

    assert sum(s_files, greedy[i := true]) <= s_disc;
    assert !isSolGreedy(s_files, s_disc, greedy);
   }
  else
   { {existTrue(s_files, s_disc, greedy, optimal, i);}
      //assert exists j :: i < j < |optima| && optima[j] == true;
      var j :| i < j < |optimal| && optimal[j] == true;
      optimal' := swap(s_files, s_disc, optimal, i, j);
   }
}

lemma sumFalse(a:seq<nat>, b:seq<bool>, i:nat)
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

lemma sumSmaller(a:seq<nat>, b:seq<bool>, i:nat)
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

lemma existTrue(s_files:seq<nat>, s_disc:nat, greedy:seq<bool>, optimal:seq<bool>, i:nat)
requires sorted(s_files[..])
requires isSolution(s_files, s_disc, greedy) && isSolution(s_files, s_disc, optimal)
requires isSolGreedy(s_files, s_disc, greedy) && isSolOptimal(s_files, s_disc, optimal)
requires 0 <= i < |optimal| == |greedy|
requires greedy[0..i] == optimal[0..i]
requires optimal[i] == false && greedy[i] == true
ensures exists j :: i < j < |optimal| && optimal[j] == true
{
  if (forall j | i < j < |optimal| :: optimal[j] == false) { 
    falseValue(s_files,optimal,i);
    assert greedy[..i+1][..|greedy[..i+1]|-1]==greedy[..i];
    assert value(greedy[..i+1]) == 1 + value(greedy[..i]);
    monotone(s_files,greedy,i+1);
    assert value(optimal) == value(optimal[..i]) == value(greedy[0..i]) < value(greedy[..i+1]);
    assert !isSolOptimal(s_files, s_disc, optimal);}
}

lemma monotone(a:seq<nat>,b:seq<bool>,i:nat)
requires 0 <= i <= |b|
ensures value(b[..i]) <= value(b)
{
  if (i == |b|) {
    assert b == b[..i];
  }
  else { calc >= {
    value(b);
    value(b[..|b|-1]) + (if b[|b|-1] then 1 else 0);
    value(b[..|b|-1]);
    //{monotone(a,b[..|b|-1],i);}
    value(b[..|b|-1][..i]);
    {assert b[..|b|-1][..i] == b[..i];}
    value(b[..i]);
  }}
}

lemma falseValue(a:seq<nat>,b:seq<bool>,i:nat)
requires 0 <= i <= |b|
requires forall k | i <= k < |b| :: b[k]==false
ensures value(b) == value(b[..i])
{
  if (i == |b|) {
    assert b == b[..i];
  }
  else { calc {
    value(b);
    value(b[..|b|-1]) + (if b[|b|-1] then 1 else 0);
    value(b[..|b|-1]);
    //{falseValue(a,b[..|b|-1]);}
    {assert b[..|b|-1][..i] == b[..i];}
    value(b[..i]);
  }}
}

//---------- 7. SWAP LEMMA ----------

lemma sumMore(a:seq<nat>,b:seq<bool>,i:nat)
requires 0 <= i < |a|==|b|
requires b[i]==false
ensures sum(a,b[i:=true])==sum(a,b)+a[i] 
{}

lemma sumLess(a:seq<nat>,b:seq<bool>,i:nat)
requires 0 <= i < |a|==|b|
requires b[i]==true
ensures sum(a,b[i:=false])==sum(a,b)-a[i] 
{}

lemma smallerSum(a:seq<nat>,b:seq<bool>,i:nat,j: nat)
requires sorted(a)
requires 0 <= i < j < |b|==|a|
requires b[i] == false && b[j] == true
ensures sum(a,b) >= sum(a,b[i:=true][j:=false])
{ calc <={
   sum(a,b[i:=true][j:=false]);
   {sumLess(a,b[i:=true],j);}
   sum(a,b[i:=true])-a[j];
   {sumMore(a,b,i);}
   sum(a,b)+a[i]-a[j];
   {assert a[i]<=a[j];}
   sum(a,b);
   }
}

lemma valueMore(a:seq<nat>,b:seq<bool>,i:nat)
requires 0 <= i < |b|
requires b[i]==false
ensures value(b[i:=true]) == value(b) + 1 
{}

lemma valueLess(a:seq<nat>,b:seq<bool>,i:nat)
requires 0 <= i < |b|
requires b[i]==true
ensures value(b[i:=false]) == value(b) - 1
{}

lemma sameValue(a:seq<nat>,b:seq<bool>,i:nat,j: nat)
requires sorted(a)
requires 0 <= i < j < |b|==|a|
requires b[i] == false && b[j] == true // Similarly the other way around
ensures value(b) == value(b[i:=true][j:=false])
{ calc =={
   value(b[i:=true][j:=false]);
   {valueLess(a,b[i:=true],j);}
   value(b[i:=true]) - 1;
   {valueMore(a,b,i);}
   value(b) + 1 - 1;
   value(b);
   }
}

ghost method swap(s_files:seq<nat>, s_disc:nat, v:seq<bool>, i: nat, j: nat) returns (v_modified:seq<bool>) 
requires sorted(s_files)
requires isSolution(s_files, s_disc, v)
requires 0 <= i < j < |v|
requires v[i] == false && v[j] == true
ensures isSolution(s_files, s_disc, v_modified) 
ensures isBetterSol(s_files,s_disc,v_modified,v)//they are equal
ensures v_modified == v[i := true][j := false]
{

  v_modified := v[i := true][j := false];
  //They have the same value
  sameValue(s_files,v,i,j);
  assert value(v_modified) == value(v);
  
  //They take up less space because t_ficheros[i] <= t_ficheros[j]
  smallerSum(s_files,v,i,j);
  assert sum(s_files, v_modified) <= sum(s_files,v) <= s_disc;
}
