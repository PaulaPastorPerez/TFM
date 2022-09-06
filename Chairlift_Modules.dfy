include "ModulesValue.dfy"

module Chairlift refines GreedyAlgorithmValue {
  datatype Maybe <T> = Nothing | Just (val:T)

  type Input = (seq<nat>, nat)
  type Elem = (nat, Maybe <nat>)

  class InputA ... {
    var weight: array<nat>;
    var k:nat

    constructor (w:array<nat>,l:nat)
    {
      weight := w;
      k := l;
      Repr := {this,weight};
    }

    predicate Valid()
    {
      Repr == {this, this.weight}
    }
  }

  class OutputA ... {
    var sol: array<Elem>;
    var size: nat; //partial output
    
    constructor (x:InputA)
      requires x.Valid()
      ensures forall z | z in Repr :: fresh(z)
      ensures Valid(x)
      ensures sol.Length == x.weight.Length
    {
      sol := new Elem[x.weight.Length];
      Repr := {this,sol};
      size := 0;
    }

    predicate Valid(x:InputA)
    {
      Repr == {this,sol} &&
      sol.Length <= x.weight.Length &&
      0 <= size <= sol.Length
    }
  }

  //NEEDED FUNCTIONS
  
  function solutionValue(x: Input, s: Solution): nat
  {
    |s|
  }

  predicate sorted(s : seq<int>) {
	  forall u, w :: 0 <= u < w < |s| ==> s[u] >= s[w]
  }

  //---------- 1. IS SOLUTION ----------

  //To guarantee existence of solution: all persons weight less that the limit
  predicate smaller(x:Input) 
  {
    forall m | 0 <= m < |x.0| :: x.0[m] <= x.1
  }

  predicate isSmaller(k:nat,s:set<nat>)
  {
    forall m | m in s :: k < m
  }

  predicate isBigger(k:nat,s:set<nat>)
  {
    forall m | m in s :: k > m
  }

  predicate isValidInput(x: Input)
  {
    sorted(x.0) && smaller(x)
  }

  function inputTrans(x:InputA) : Input
  { 
    (x.weight[..],x.k)
  }

  function outputTrans(x:InputA, y:OutputA) : Solution
  {
    //(y.sol)[..]
    (y.sol)[..y.size]
  }

  //The generalised version when all persons are sat
  predicate isSolution(x:Input, s:Solution)
  ensures isSolution(x,s) ==> forall p | p in s :: 0 <= p.0 < |x.0|
  ensures isSolution(x,s) ==> forall p | p in s && p.1!=Nothing :: 0<= p.1.val < |x.0|
  {
    isSolutionG((set i | 0<=i<|x.0|),x,s)
  }

  lemma lisSolution(n:nat, x:Input, s:Solution)
  requires isValidInput(x)
  requires isSolution(x,s) 
  requires  0 <= n < |x.0| 
  ensures (exists p :: p in s && (p.0==n || (p.1!=Nothing  && p.1.val==n)))
  {
    lallPerson(n,(set i | 0<=i<|x.0|),s);
  }

  //Generalised version of isSolution where index represents the indices of people to seat
  //If index==(set i | 0<=i<|weight|) we have a full solution
  predicate isSolutionG(index:set<nat>, x:Input, s:Solution)
  requires isValidInput(x)
  requires index <= set n | 0 <= n < |x.0|
  ensures isSolutionG(index,x,s) ==> forall p | p in s :: p.0 in index
  ensures isSolutionG(index,x,s) ==> forall p | p in s && p.1!=Nothing :: p.1.val in index
  ensures isSolutionG(index,x,s) ==> forall i | i in index :: (exists p :: p in s && (p.0==i || (p.1!=Nothing  && p.1.val==i)))
  {
    |s| <= |x.0| &&
    firstSmaller(s) && sortedFirst(s) && 
    allPerson(index,s) && 
    (forall z | z in s && z.1 != Nothing :: (x.0)[z.0] + (x.0)[(z.1).val] <= x.1)
  }

  //---------- 1.1 AUXILIARS PREDICATES ----------

  //First the heavier (less index) then the thinner (higher index)
  predicate firstSmaller(s:Solution)
  { 
    forall p | p in s && p.1 != Nothing :: p.0 < (p.1).val
  }

  //To compare different solutions sort them from heavier to thinner
  predicate sortedFirst(s:Solution)
  {
    forall x,y | 0 <= x < y < |s| :: s[x].0 < s[y].0
  }

  function set_of(xs: Solution): set<nat>
  {
    (set p | p in xs :: p.0) +
    (set p | p in xs && p.1!=Nothing :: p.1.val)
  }

  //Two lemmas to prove that set_of collects non-Nothing components of the pairs in xs and only those
  lemma collects_all (xs: Solution) // En el conjunto estan todas las componentes no Nothing 
  ensures forall p | p in xs :: p.0 in set_of(xs)
  ensures forall p | p in xs && p.1!=Nothing :: p.1.val in set_of(xs)
  {}

  lemma noMore(xs: Solution) //What it is in the set, it has to come from some pair 
  ensures forall i | i in set_of(xs) :: (exists p :: p in xs && (p.0==i || (p.1!=Nothing && p.1.val==i)))
  ensures set_of(xs)=={} ==> xs==[]  
  {
    if (set_of(xs)=={}) {
      assume xs!=[];
      collects_all(xs);
      assert xs[0].0 in set_of(xs);}
  }

  //All people in index and only those are sat exactly once
  predicate allPerson(index:set<nat>,sol:Solution)
  ensures allPerson(index,sol) ==> forall p | p in sol :: p.0 in index
  ensures allPerson(index,sol) ==> forall p | p in sol && p.1!=Nothing :: p.1.val in index
  ensures allPerson(index,sol) ==> forall i | i in index :: (exists p :: p in sol && (p.0==i || (p.1!=Nothing  && p.1.val==i)))
  {
    collects_all(sol);
    noMore(sol);
    noRepetitions(sol) &&
    //everybody in the solution
    set_of(sol) == index
  }

  lemma lallPerson(i:nat,index:set<nat>,sol:Solution)
  requires allPerson(index,sol) && i in index
  ensures (exists p :: p in sol && (p.0==i || (p.1!=Nothing  && p.1.val==i)))
  {}

  predicate noRepetitions(sol:Solution)
  {
    //All firts different :: already in firstSmaller
    //All seconds different
    (forall x,y | 0 <= x < y < |sol| && sol[x].1 != Nothing && sol[y].1 != Nothing :: sol[x].1.val != sol[y].1.val ) &&
    //The first ones different from the second ones
    (forall x,y | 0 <= x < |sol| && 0 <= y < |sol| && sol[y].1 != Nothing :: sol[x].0 != sol[y].1.val)
    //x != y not necessary due to firstSmaller
  }

  //---------- 1.2. EXISTENCE OF SOLUTION ----------

  lemma existsSolution(x:Input)
  {
    var sol := seq(|x.0|, n => (n,Nothing));

    {everyoneAlone(x,(set i | 0<=i<|x.0|),sol,|sol|);}
    assert isSolution(x,sol);
  }

  lemma everyoneAlone(x:Input, index:set<nat>, sol:Solution, i:nat)
  requires isValidInput(x)
  requires |x.0| == |sol| && forall j | 0 <= j < |x.0| :: sol[j] == (j,Nothing)
  requires index == (set j | 0 <= j < i)
  requires 0 <= i <= |sol|
  ensures set_of(sol[..i]) == index;
  {
    if (i == 0) {}
    else {
      assert sol[i-1] == (i-1,Nothing);
      assert set_of(sol[..i]) == set_of(sol[..i-1]) + {i-1};
      assert index == (set j | 0 <= j < i-1) + {i-1};
      {everyoneAlone(x,(set j | 0 <= j < i-1),sol,i-1);}
    }
  }

  //---------- 2. IS BETTER SOLUTION ----------

  //Given two solutions possibles of the problem, for one solution to be the best one it
  //has to verify that it uses less chairlift.
  predicate isBetterSol(x:Input, s1:Solution, s2:Solution)

  lemma isBetterSolTrans(x:Input, s1:Solution, s2:Solution, s3:Solution)

  lemma isBetterSolRefl(x:Input, s:Solution)
  
  //---------- 3. IS GREEDY SOLUTION ----------

  //---------- AUXILIARS PREDICATES ----------

  //Range of values of the first and second components of pairs
  predicate values(len:nat,sol:Solution,i:nat,j:int)
  requires 0<=i<=j+1<=len && |sol|==i
  { 
    forall x | 0 <= x < i  :: 0 <= sol[x].0 < i &&
    forall x | 0 <= x < i && sol[x].1 != Nothing :: j < sol[x].1.val < len
  }

  //First components are always the smallest index (highest weight) of remaining people
  predicate theSmallest(len:nat,sol:Solution,i:nat)
  requires 0<=i<=len && |sol|==i<=len
  { 
    var allIndex:= set n | 0 <= n < len; 
    forall x | 0 <= x < i :: isSmaller(sol[x].0,allIndex-set_of(sol[..x+1]))
  }

  //Second non-Nothing components are always the biggest (least weight) index of remaining people
  predicate theBiggest(len:nat,sol:Solution,i:nat)
  requires 0<=i<=len && |sol|==i<=len
  { 
    var allIndex:= set n | 0 <= n < len; 
    forall x | 0 <= x < i && sol[x].1 != Nothing:: isBigger(sol[x].1.val,allIndex-set_of(sol[..x+1]))
  }

  //i cannot seat with the one in the set s
  predicate cannotSeat(x:Input,i:nat,s:set<nat>)
  requires 0<=i<|x.0| && forall z | z in s :: 0<=z<|x.0| 
  {
    forall z | z in s :: (x.0)[i] + (x.0)[z] > x.1 
  }

  //Second Nothing component means first component cannot seat with any remaining person
  predicate notPostpone(x:Input,sol:Solution,i:nat,j:int)
  requires 0<=i<=j+1<=|x.0| && |sol|==i
  requires values(|x.0|,sol,i,j)
  { 
    var allIndex:= set n | 0 <= n < |x.0|; 
    forall y | 0 <= y < i && sol[y].1 == Nothing :: cannotSeat(x,sol[y].0,allIndex-set_of(sol[..y+1]))
  }

  //---------- DEFINITION SOL GREEDY ----------

  //Generalised version of isSolGreedy where index is the set of people already seated
  //that we know are in [0..i)+[j+1..|weight|)
  predicate isSolGreedyG(index:set<nat>, x:Input, sol:Solution,i:nat,j:int) //j may be -1 
  requires isValidInput(x) && |sol|==i
  requires 0<=i<=j+1<=|x.0|
  requires index==(set n | 0 <= n < i) + (set n | j < n < |x.0|)
  requires isSolutionG(index,x,sol)
  {
    values(|x.0|,sol,i,j) &&
    theSmallest(|x.0|,sol,i) &&
    theBiggest(|x.0|,sol,i) &&
    notPostpone(x,sol,i,j)
  }

  //When the algorithm ends everybody is seated and i==j+1==|sol|
  predicate isSolGreedy(x:Input, s:Solution)
  { 
    isSolGreedyG(set n | 0 <= n < |x.0|,x,s,|s|,|s|-1)
  }

  //---------- 4. IS OPTIMAL SOLUTION ----------

  predicate isSolOptimal(x:Input, s:Solution)

  lemma betterThanOptimal(x:Input, s:Solution, optimalS:Solution)

  //---------- 5. ALGORITHM ----------
  //---------- AUXILIARS LEMMAS ----------

  lemma equalSequences<A>(xs:seq<A>,ys:seq<A>,j:nat,i:nat)
  requires 0 <= i < j <= |xs| <= |ys|
  requires xs[..j]==ys[..j]
  ensures xs[..i]==ys[..i] && xs[i]==ys[i]
  {}

  lemma {:verify true} restoreGreedy1(x:Input, sol:Solution, i:nat, j:nat)
  requires 0 <= i < j <= |x.0|-1 && |sol|==i
  requires isValidInput(x)
  requires set_of(sol) == (set n | 0 <= n < i) + (set n | j < n < |x.0|)
  requires isSolutionG(set_of(sol),x,sol)
  requires isSolGreedyG(set_of(sol),x,sol,i,j)
  requires (x.0)[i] + (x.0)[j] <= x.1
  ensures isSolutionG(set_of(sol)+{i,j},x,sol+[(i,Just (j))])
  ensures isSolGreedyG(set_of(sol)+{i,j},x,sol+[(i,Just (j))],i+1,j-1)
  {
    assert values(|x.0|,sol+[(i,Nothing)],i+1,j);

    var allIndex := set n | 0 <= n < |x.0|; 
    forall y | 0 <= y < i+1
    ensures isSmaller((sol+[(i,Just (j))])[y].0,allIndex-set_of((sol+[(i,Just (j))])[..y+1]))
    { 
      if (y < i) {
        assert (sol+[(i,Just (j))])[..y+1]==sol[..y+1];
      }
      else {
        assert set_of(sol+[(i,Just (j))])==set_of(sol)+{i,j};
        assert (sol+[(i,Just (j))])[y].0==i;
        assert (sol+[(i,Just (j))])[..y+1]==sol+[(i,Just (j))];
        assert isSmaller(i,allIndex-set_of(sol+[(i,Just (j))]));
      }
    }

    forall y | 0 <= y < i+1 && (sol+[(i,Just (j))])[y].1 != Nothing
    ensures isBigger((sol+[(i,Just (j))])[y].1.val,allIndex-set_of((sol+[(i,Just (j))])[..y+1]))
    {
      if (y < i) {
        assert (sol+[(i,Just (j))])[..y+1]==sol[..y+1];
      }
      else {
        assert (sol+[(i,Just (j))])[..y+1]==sol+[(i,Just (j))];
        assert set_of(sol+[(i,Just (j))])== set_of(sol)+{i,j};
        assert set_of(sol+[(i,Just (j))]) == (set n | 0 <= n < i+1) + (set n | j <= n < |x.0|);
      }
    }
  
    forall y | 0 <= y < i+1 && (sol+[(i,Just (j))])[y].1 == Nothing
    ensures cannotSeat(x,(sol+[(i,Just (j))])[y].0,allIndex-set_of((sol+[(i,Just (j))])[..y+1]))
    {
      if (y < i) {
        assert (sol+[(i,Just (j))])[..y+1]==sol[..y+1];
        assert (sol+[(i,Just (j))])[y].0==sol[y].0;    
      } 
      else {}
    }
  }

  lemma {:verify true} restoreGreedy2(x:Input, sol:Solution, i:nat, j:nat)
  requires 0 <= i < j <= |x.0|-1 && |sol|==i
  requires isValidInput(x)
  requires set_of(sol) == (set n | 0 <= n < i) + (set n | j < n < |x.0|)
  requires isSolutionG(set_of(sol),x, sol)
  requires isSolGreedyG(set_of(sol),x,sol,i,j)
  requires (x.0)[i] + (x.0)[j] > x.1
  ensures isSolutionG(set_of(sol)+{i},x,sol+[(i,Nothing)])
  ensures isSolGreedyG(set_of(sol)+{i},x,sol+[(i,Nothing)],i+1,j)
  {
    assert values(|x.0|,sol+[(i,Nothing)],i+1,j);

    var allIndex := set n | 0 <= n < |x.0|; 
    forall z | 0 <= z < i+1
    ensures isSmaller((sol+[(i,Nothing)])[z].0,allIndex-set_of((sol+[(i,Nothing)])[..z+1]))
    {
      if (z < i) {
        assert (sol+[(i,Nothing)])[..z+1]==sol[..z+1];
        //assert (sol+[(i,Nothing)])[z].0==sol[z].0;    
      }
      else {
        assert set_of(sol+[(i,Nothing)])==set_of(sol)+{i};
        assert (sol+[(i,Nothing)])[z].0==i;
        assert (sol+[(i,Nothing)])[..z+1]==sol+[(i,Nothing)];
        assert isSmaller(i,allIndex-set_of(sol+[(i,Nothing)]));
      }
    }

    forall z | 0 <= z < i+1 && (sol+[(i,Nothing)])[z].1 != Nothing
    ensures isBigger((sol+[(i,Nothing)])[z].1.val,allIndex-set_of((sol+[(i,Nothing)])[..z+1]))
    {
      if (z < i) {
        assert (sol+[(i,Nothing)])[..z+1]==sol[..z+1];
      }
      else {}
    }

    forall z | 0 <= z < i+1 && (sol+[(i,Nothing)])[z].1 == Nothing
    ensures cannotSeat(x,(sol+[(i,Nothing)])[z].0,allIndex-set_of((sol+[(i,Nothing)])[..z+1]))
    {
      if (z < i) {
        assert (sol+[(i,Nothing)])[..z+1]==sol[..z+1];
        assert (sol+[(i,Nothing)])[z].0==sol[z].0;    
      }
      else{
        assert (sol+[(i,Nothing)])[..z+1]==sol+[(i,Nothing)];
        assert set_of(sol+[(i,Nothing)])== (set n | 0 <= n < i+1) + (set n | j < n < |x.0|);
      }
    }
  }

  lemma {:verify true} restoreGreedy3(y:Input, sol:Solution, i:nat, j:nat)
  requires 0<= i==j <= |y.0|-1 && |sol|==i
  requires isValidInput(y)
  requires set_of(sol) == (set n | 0 <= n < i) + (set n | j < n < |y.0|)
  requires isSolutionG(set_of(sol),y,sol)
  requires isSolGreedyG(set_of(sol),y,sol,i,j)
  ensures isSolutionG(set_of(sol)+{i},y,sol+[(i,Nothing)])
  ensures isSolGreedyG(set_of(sol)+{i},y,sol+[(i,Nothing)],i+1,j)
  {
    assert values(|y.0|,sol+[(i,Nothing)],i+1,j);

    var allIndex := set n | 0 <= n < |y.0|; 
    assert (sol+[(i,Nothing)])[..i+1]==sol+[(i,Nothing)];
    assert set_of(sol+[(i,Nothing)])== (set n | 0 <= n < i+1) + (set n | i < n < |y.0|) ;
    assert set_of(sol+[(i,Nothing)])== (set n | 0 <= n < |y.0|) == allIndex;
    assert allIndex-set_of((sol+[(i,Nothing)])[..i+1])=={};

    forall x | 0 <= x < i+1
    ensures isSmaller((sol+[(i,Nothing)])[x].0,allIndex-set_of((sol+[(i,Nothing)])[..x+1]))
    {
      if (x < i) {
        assert (sol+[(i,Nothing)])[..x+1]==sol[..x+1];
      }
      else {}
    }

    forall x | 0 <= x < i+1 && (sol+[(i,Nothing)])[x].1 != Nothing
    ensures isBigger((sol+[(i,Nothing)])[x].1.val,allIndex-set_of((sol+[(i,Nothing)])[..x+1]))
    {
      if (x < i) {
        assert (sol+[(i,Nothing)])[..x+1]==sol[..x+1];
      }
      else {}
    }

    forall x | 0 <= x < i+1 && (sol+[(i,Nothing)])[x].1 == Nothing
    ensures cannotSeat(y,(sol+[(i,Nothing)])[x].0,allIndex-set_of((sol+[(i,Nothing)])[..x+1]))
    {
      if (x < i) {
        assert (sol+[(i,Nothing)])[..x+1]==sol[..x+1];
      }
      else {} 
    }
  }

  //---------- ALGORITHM ----------

  method greedy(x:InputA) returns (res:OutputA)
  {
    var j := (x.weight).Length-1;
    res := new OutputA(x);
    res.size := 0;
    
    while (res.size < j)
      decreases j-(res.size)
      invariant 0 <= res.size <= j+1 && (res.size)-1 <= j < (x.weight).Length
      invariant 0 <= res.sol.Length == (x.weight).Length
      invariant set_of((res.sol)[..res.size]) == (set n | 0 <= n < res.size) + (set n | j < n < (x.weight).Length)
      invariant isSolutionG(set_of((res.sol)[..res.size]),inputTrans(x),(res.sol)[..res.size])   
      invariant isSolGreedyG(set_of((res.sol)[..res.size]),inputTrans(x),(res.sol)[..res.size],res.size,j)
      //To be able to fill the solution array
      invariant forall z | z in res.Repr :: fresh(z)
      invariant res.Valid(x)
      { 
        assert res.size < j;
        if (x.weight)[res.size] + (x.weight)[j] <= x.k { //they can go together
          (res.sol)[res.size] := (res.size, Just (j));
          restoreGreedy1(inputTrans(x),(res.sol)[..res.size],res.size,j);
          assert (res.sol)[..res.size+1] == (res.sol)[..res.size] + [(res.size,Just (j))];
          j := j-1;
        }
        else { //they can not go together
          (res.sol)[res.size] := (res.size, Nothing);
          restoreGreedy2(inputTrans(x), (res.sol)[..res.size],res.size,j);
          assert (res.sol)[..res.size+1]==(res.sol)[..res.size]+[(res.size,Nothing)];
        }
        res.size := res.size + 1;
        //assert isSolGreedyG(set_of((res.0)[..res.1]),inputTrans(x),(res.0)[..res.1],res.1,j);
      }

    if (res.size==j) //there is one person left, it has to go alone in the chairlift
    {
      (res.sol)[res.size] := (res.size, Nothing);
      assert set_of((res.sol)[..res.size+1])==set_of((res.sol)[..res.size])+{res.size};
      assert (res.sol)[..res.size+1]==(res.sol)[..res.size]+[(res.size,Nothing)];
      restoreGreedy3(inputTrans(x), (res.sol)[..res.size],res.size,j);

      res.size := res.size + 1;
    }

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

  lemma {:verify true} sameSol(x:Input, sol1:Solution, sol2:Solution)
  requires isValidInput(x)
  requires isSolution(x,sol1) && isSolution(x,sol2)
  requires |sol1| <= |sol2|
  requires sol1 == sol2[..|sol1|]
  ensures |sol1| == |sol2|
  ensures sol1 == sol2
  {
    if |sol1| == |sol2| {}
    else {
      //assert set_of(sol1) == set n | 0 <= n < |weight|;
      //assert set_of(sol1) == set_of(sol2[..|sol1|]);
      assert set_of(sol2[|sol1|..]) == {};
      noMore(sol2[|sol1|..]);
      assert sol2[|sol1|..]==[];
    }
  }

  ghost method {:verify false} reduction_step(x:Input, greedy:Solution, optimal:Solution, i:nat) returns (optimal':Solution)
  {
    var allIndex := set n | 0 <= n < |x.0|;
    assert set_of(greedy[i..])==allIndex-set_of(greedy[..i]);
    assert set_of(optimal[i..]) == allIndex-set_of(optimal[..i]);
    assert set_of(greedy[i..])==set_of(optimal[i..]);

    sameInI(x,optimal,greedy,i);
    assert greedy[i].0 == optimal[i].0 && greedy[i].1 != optimal[i].1;

    if (greedy[i].1 == Nothing) //&& optimal[i].1 != Nothing
    {//Impossible

      assert x.0[greedy[i].0] + x.0[optimal[i].1.val] <= x.1;

      var j := optimal[i].1.val;
      existsZ(x,optimal,greedy,i,j);

      var z :| i < z < |greedy| && (greedy[z].0 == j || greedy[z].1 == Just (j));
      assert (x.0[greedy[i].0] + (x.0)[greedy[z].0] <= x.1) || (greedy[z].1 == Just (j) && (x.0)[greedy[i].0] + (x.0)[greedy[z].1.val] <= x.1);
      assert !isSolGreedy(x,greedy);
    }
    else {
      var j := greedy[i].1.val;
      existsZ(x,greedy,optimal,i,j);
      var z :| i < z < |optimal| && (optimal[z].0 == j || optimal[z].1 == Just (j));

      if (optimal[i].1 == Nothing) {
        if (optimal[z].0 == j) { 
          //Prove first that optimal[z].1 != Nothing by contradiction
          if optimal[z].1 == Nothing {
            lessChairlift(x,optimal,i,z);
            assert !isSolOptimal(x,optimal);
          }
          else {
            optimal':=swapFirstSecond(x,optimal,i,z);
            assert optimal'[0..i+1]==optimal'[0..i]+[optimal'[i]];
          }
        }
        else { //optimal[z] = (_,j)
          optimal' := move(x,optimal,i,z);
          assert optimal'[0..i+1]==optimal'[0..i]+[optimal'[i]];
        }
      }
      else { //optimal[i].1 != Nothing 
        if (optimal[z].0 == j) {
          //Prove first that optimal[z].1 == Nothing by contradiction
          assert forall n | n in allIndex-set_of(greedy[..i+1]) :: greedy[i].1.val > n;
          assert greedy[..i+1] == greedy[..i] + [greedy[i]];
          assert set_of(greedy[..i+1]) == set_of(greedy[..i]) + {greedy[i].0,greedy[i].1.val};
          if optimal[z].1 != Nothing {
            assert optimal[z].1.val in allIndex-set_of(greedy[..i+1]);
            assert greedy[i].1.val == optimal[z].0  < optimal[z].1.val;
            assert !isSolution(x,optimal);
          }
          else {
            optimal' := swapSecondFirst(x,optimal,i,z);
            assert optimal'[0..i+1] == optimal'[0..i]+[optimal'[i]];
          }
        }
        else { 
          optimal' := swapSecond(x,optimal,i,z);
          assert optimal'[0..i+1] == optimal'[0..i]+[optimal'[i]];
        }
      }
    }
  }

  lemma {:verify true} lessChairlift(x:Input, optimal:Solution, i:nat, z:nat)
  requires isValidInput(x)
  requires isSolution(x,optimal) && isSolOptimal(x,optimal)
  requires 0 <= i < z < |optimal|
  requires optimal[i].1 == Nothing && optimal[z].1 == Nothing
  requires (x.0)[optimal[i].0] + (x.0)[optimal[z].0] <= x.1
  ensures !isSolOptimal(x,optimal)
  {
    var auxSol := optimal[i:=(optimal[i].0, Just (optimal[z].0))];
    var auxSol2 := auxSol[..z] + auxSol[z+1..];

    set_ofPropertyAdd(optimal,i,optimal[z].0);
    assert set_of(auxSol2) == set_of(optimal);
    assert isSolution(x,auxSol2);
    //assert isBetterSol(weight,k,auxSol2,optimal);
  }

  lemma {:verify true} set_ofPropertyAdd(sol:Solution, i:nat, a:nat)
  requires 0 <= i < |sol| && sol[i].1 == Nothing
  ensures set_of(sol[i := (sol[i].0, Just (a))]) == set_of(sol) + {a}
  {
    var sol2 :| sol2 == sol[i := (sol[i].0, Just (a))];
    assert set_of(sol) == (set p | p in sol :: p.0) + (set p | p in sol && p.1 != Nothing :: p.1.val);
    assert set_of(sol2) == (set p | p in sol2 :: p.0) + (set p | p in sol2 && p.1 != Nothing :: p.1.val);

    assert forall i | 0 <= i < |sol| == |sol2| :: sol[i].0 == sol2[i].0;
    assert (set p | p in sol :: p.0) == (set p | p in sol2 :: p.0);
  }

  lemma {:verify true} sameInI(x:Input, sol1:Solution, sol2:Solution, i:nat)
  requires isValidInput(x)
  requires 0 <= i < |sol1| <= |sol2|
  requires isSolution(x,sol1) && isSolution(x,sol2)
  requires sol1[..i] == sol2[..i]
  ensures sol1[i].0 == sol2[i].0
  { 
    assert set_of(sol1[..i]) == set_of(sol2[..i]);
  }

  lemma {:verify true} existsZ(x:Input, sol1:Solution, sol2:Solution, i:nat, j:nat)
  requires isValidInput(x)
  requires isSolution(x, sol1) 
  requires isSolution(x, sol2) 
  requires 0 <= i < |sol2| && 0 <= i < |sol1| && 0 <= j < |x.0|
  requires sol1[i].1 != Nothing && j == sol1[i].1.val
  requires sol2[..i] == sol1[0..i] && sol1[i].0 == sol2[i].0 && sol1[i].1 != sol2[i].1
  ensures exists z :: i < z < |sol2| && ((sol2[z].0 == j) || sol2[z].1 == Just (j))
  {
    assert set_of(sol2[..i]) == set_of(sol1[0..i]);
    assert sol1[i].1.val !in set_of(sol2[0..i]);
    assert sol1[i].1.val in set_of(sol2[i..]);
  }

  //---------- 7. SWAP LEMMA ----------

  //Inserts a valid pair with components that were not in the sol.
  //It returns the new solution and the position where it was inserted.
  function {:verify true} insert(index:set<nat>,x:Input,p:Elem,sol:Solution,i:nat):(Solution,nat)
  requires isValidInput(x) && |sol|<|x.0|
  requires index <= set n | 0 <= n < |x.0|
  requires isSolutionG(index,x,sol)
  requires 0 <= p.0 < |x.0| && p.0 !in index
  requires p.1 != Nothing ==> p.1.val !in index && 0 <= p.0 < p.1.val < |x.0| && (x.0)[p.0] + (x.0)[(p.1).val] <= x.1
  requires 0 <= i <= |sol|
  requires forall z | 0 <= z < i :: sol[z].0 < p.0
  ensures |insert(index,x,p,sol,i).0| == 1+|sol|
  ensures 0 <= insert(index,x,p,sol,i).1 < |insert(index,x,p,sol,i).0| && insert(index,x,p,sol,i).0[insert(index,x,p,sol,i).1]==p
  ensures forall z | 0 <= z < insert(index,x,p,sol,i).1 :: sol[z].0 < p.0
  ensures forall z | insert(index,x,p,sol,i).1 <= z < |sol| :: sol[z].0 > p.0
  ensures insert(index,x,p,sol,i).0[..insert(index,x,p,sol,i).1] == sol[..insert(index,x,p,sol,i).1]
  ensures insert(index,x,p,sol,i).0[insert(index,x,p,sol,i).1+1..] == sol[insert(index,x,p,sol,i).1..]
  ensures p.1 == Nothing ==> isSolutionG(index+{p.0},x,insert(index,x,p,sol,i).0)
  ensures p.1 != Nothing ==>  isSolutionG(index+{p.0,p.1.val},x,insert(index,x,p,sol,i).0)
  decreases |sol| - i
  { 
    if i == |sol| then 
      assert p.1 == Nothing ==> isSolutionG(index+{p.0},x,sol+[p]);
      assert p.1 != Nothing ==> |sol + [p]| <= |x.0|;
      assert p.1 != Nothing ==>  isSolutionG(index+{p.0,p.1.val},x,sol+[p]);
      (sol + [p],i)
    else
      assert 0 <= i < |sol|;
      if sol[i].0 > p.0 then
        (sol[..i] + [p] + sol[i..], i)
      else
        insert(index,x,p,sol,i+1)
  }

  //Replace the second component from a pir for another valid one
  function {:verify true} replace(index:set<nat>,x:Input,sol:Solution,i:nat,j:Maybe<nat>):Solution
  requires isValidInput(x) && |sol|<=|x.0|
  requires index <= set n | 0 <= n < |x.0|
  requires isSolutionG(index,x,sol)
  requires 0 <= i < |sol|
  requires j != Nothing ==> j.val !in index && 0 <= sol[i].0 < j.val < |x.0| && (x.0)[sol[i].0] + (x.0)[j.val] <= x.1
  ensures |replace(index,x,sol,i,j)| == |sol|
  ensures replace(index,x,sol,i,j)[i] == (sol[i].0,j)
  ensures replace(index,x,sol,i,j)[..i] == sol[..i] && replace(index,x,sol,i,j)[i+1..] == sol[i+1..] 
  ensures j == Nothing && sol[i].1 == Nothing ==> isSolutionG(index,x,replace(index,x,sol,i,j))
  ensures j == Nothing && sol[i].1 != Nothing ==> isSolutionG(index-{sol[i].1.val},x,replace(index,x,sol,i,j))
  ensures j != Nothing && sol[i].1 == Nothing ==>  isSolutionG(index+{j.val},x,replace(index,x,sol,i,j))
  ensures j != Nothing && sol[i].1 != Nothing ==>  isSolutionG(index+{j.val}-{sol[i].1.val},x,replace(index,x,sol,i,j))
  { 
    assert sol == sol[..i] + [sol[i]] + sol[i+1..];
    sol[..i] + [(sol[i].0,j)] + sol[i+1..]
  }

  //Deletes a pair from some given position
  function {:verify true} delete(index:set<nat>,x:Input,p:Elem,i:nat,sol:Solution):Solution
  requires isValidInput(x) && |sol| <= |x.0|
  requires index <= set n | 0 <= n < |x.0|
  requires isSolutionG(index,x,sol)
  requires 0 <= i < |sol| && sol[i] == p
  ensures p !in delete(index,x,p,i,sol) 
  ensures delete(index,x,p,i,sol) == sol[..i]+sol[i+1..]
  ensures p.1 == Nothing ==> isSolutionG(index-{p.0},x,delete(index,x,p,i,sol))
  ensures p.1 != Nothing ==>  isSolutionG(index-{p.0,p.1.val},x,delete(index,x,p,i,sol))
  {
    sol[..i]+sol[i+1..]
  }

  ghost method {:verify true} swapFirstSecond(x:Input, v:Solution, i:nat, z:nat) returns (v_modified:Solution) 
  requires isValidInput(x)
  requires isSolution(x,v)
  requires 0 <= i < z < |v| <= |x.0|
  requires v[i].1 == Nothing && v[z].1 != Nothing 
  requires v[i].0 < v[z].0
  requires (x.0)[v[i].0] + (x.0)[v[z].0] <= x.1
  ensures |v_modified| == |v| && v_modified[..i] == v[..i] && v_modified[i] == (v[i].0,Just (v[z].0))
  ensures isSolution(x,v_modified) 
  ensures isBetterSol(x,v_modified,v)//they are equal
  {
    var allIndex := set n | 0 <= n < |x.0|;
    v_modified := delete(allIndex,x,v[z],z,v);
    var index := allIndex - {v[z].0,v[z].1.val};
    assert v_modified[..z] == v[..z];

    v_modified := replace(index,x,v_modified,i,Just (v[z].0));
    index := index + {v[z].0};
    assert v_modified[..i] == v[..i] && v_modified[i] == (v[i].0, Just (v[z].0));

    var pair:=insert(index,x,(v[z].1.val,Nothing),v_modified,0); 
    index:=index+{v[z].1.val};

    assert i < pair.1 <= |v_modified|<=|pair.0| ;
    assert pair.0[..pair.1] == v_modified[..pair.1];
    equalSequences(v_modified,pair.0,pair.1,i);
    assert pair.0[..i] == v_modified[..i] == v[..i] && pair.0[i] == v_modified[i] == (v[i].0,Just (v[z].0));

    v_modified:=pair.0;
    assert isSolutionG(allIndex,x,v_modified);
  }

  ghost method {:verify true} swapSecondFirst(x:Input, v:Solution, i:nat, z:nat) returns (v_modified:Solution) 
  requires isValidInput(x)
  requires isSolution(x,v)
  requires 0 <= i < z < |v|<=|x.0|
  requires v[i].1 != Nothing && v[z].1 == Nothing 
  requires v[i].0 < v[z].0 
  requires (x.0)[v[i].0] + (x.0)[v[z].0] <= x.1
  ensures |v_modified| == |v| && v_modified[..i] == v[..i] && v_modified[i]==(v[i].0,Just (v[z].0))
  ensures isSolution(x,v_modified) 
  ensures isBetterSol(x,v_modified,v)//they are equal
  {
    var allIndex := set n | 0 <= n < |x.0|;
    v_modified := delete(allIndex,x,v[z],z,v);
    var index := allIndex-{v[z].0};
    assert v_modified[..z] == v[..z];

    v_modified := replace(index,x,v_modified,i,Just (v[z].0));
    index := index-{v[i].1.val}+{v[z].0};
    assert v_modified[..i] == v[..i] && v_modified[i] == (v[i].0, Just (v[z].0));
  
    var pair := insert(index,x,(v[i].1.val,Nothing),v_modified,0); 
    index := index + {v[i].1.val};

    assert i < pair.1 <= |v_modified| <= |pair.0| ;
    assert pair.0[..pair.1] == v_modified[..pair.1];
    equalSequences(v_modified,pair.0,pair.1,i);
    assert pair.0[..i] == v_modified[..i] == v[..i] && pair.0[i] == v_modified[i] == (v[i].0,Just (v[z].0));

    v_modified := pair.0;
    assert isSolutionG(allIndex,x,v_modified);
  } 

  ghost method {:verify true} move(x:Input, v:Solution, i:nat, z:nat) returns (v_modified:Solution) 
  requires isValidInput(x)
  requires isSolution(x,v)
  requires 0 <= i < z < |v|<=|x.0|
  requires v[i].1 == Nothing && v[z].1 != Nothing 
  requires v[i].0 < v[z].1.val 
  requires (x.0)[v[i].0] + (x.0)[v[z].1.val] <= x.1
  ensures |v_modified| == |v| && v_modified[..i]==v[..i] && v_modified[i] == (v[i].0,v[z].1)
  ensures isSolution(x,v_modified) 
  ensures isBetterSol(x,v_modified,v)//they are equal
  {   
    var allIndex := set n | 0 <= n < |x.0|;
    v_modified := replace(allIndex,x,v,z,Nothing);
    v_modified := replace(allIndex-{v[z].1.val},x,v_modified,i,v[z].1);
  }

  ghost method {:verify true} swapSecond(x:Input, v:Solution, i:nat, z:nat) returns (v_modified:Solution) 
  requires isValidInput(x)
  requires isSolution(x,v)
  requires 0 <= i < z < |v|<=|x.0|
  requires v[i].1 != Nothing && v[z].1 != Nothing 
  requires v[i].0 < v[z].1.val 
  requires (x.0)[v[i].0] + (x.0)[v[z].1.val] <= (x.1)
  ensures |v_modified| == |v| && v_modified[..i] == v[..i] && v_modified[i] == (v[i].0,v[z].1)
  ensures isSolution(x,v_modified) 
  ensures isBetterSol(x,v_modified,v)//they are equal
  {     
    var allIndex := set n | 0 <= n < |(x.0)|;
    v_modified := delete(allIndex,x,v[z],z,v);
    assert v_modified[..z] == v[..z];
    var index := allIndex - {v[z].0,v[z].1.val};

    v_modified := replace(index,x,v_modified,i,v[z].1);
    index := index+{v[z].1.val} - {v[i].1.val};
    assert v_modified[..i] == v[..i] && v_modified[i] == (v[i].0,v[z].1);

    var pair;
    if (v[z].0 < v[i].1.val) { 
      pair := insert(index,x,(v[z].0,v[i].1),v_modified,0);
    }
    else {
      pair := insert(index,x,(v[i].1.val,Just (v[z].0)),v_modified,0);
    }

    assert i < pair.1 <= |v_modified| <= |pair.0|;
    assert pair.0[..pair.1] == v_modified[..pair.1];
    equalSequences(v_modified,pair.0,pair.1,i);
    assert pair.0[..i] == v_modified[..i]==v[..i] && pair.0[i] == v_modified[i] == (v[i].0,v[z].1);

    v_modified := pair.0;
    assert isSolutionG(allIndex,x,v_modified);
  }
}