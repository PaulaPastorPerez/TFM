abstract module GreedyAlgorithm {

    type Input(!new, ==) // Immutable input data
    type Elem(!new, ==)   // Immutable solution elements

    class InputA {
      ghost var Repr:set<object>

      predicate Valid()
      reads this, Repr
    }

    class OutputA {
      ghost var Repr:set<object>

      predicate Valid(x:InputA)
      reads this, Repr, x, x.Repr
      requires x.Valid()
    }
  
    type Solution = seq<Elem>

    predicate isValidInput(x:Input)

    function inputTrans(x: InputA) : Input
    reads x, x.Repr
    requires x.Valid()

    method inputRecover(x: Input) returns (s: InputA)
    ensures s.Valid()
    ensures inputTrans(s) == x


    function outputTrans(x: InputA,y: OutputA) : Solution
    reads x, x.Repr, y, y.Repr
    requires x.Valid() && y.Valid(x)

    method outputRecover(xA: InputA, y: Solution) returns (s: OutputA)
    requires xA.Valid()
    requires isValidInput(inputTrans(xA))
    requires isSolution(inputTrans(xA), y)
    ensures s.Valid(xA)
    ensures outputTrans(xA, s) == y

    // ------- 1. PREDICATES -------

    predicate isSolution(x:Input, s:Solution)
    requires isValidInput(x)

    predicate isBetterSol(x:Input, s1:Solution, s2:Solution)
    requires isValidInput(x)
    requires isSolution(x,s1) && isSolution(x,s2)

    lemma isBetterSolTrans(x:Input, s1:Solution, s2:Solution, s3:Solution)
    requires isValidInput(x)
    requires isSolution(x,s1) && isSolution(x,s2) && isSolution(x,s3)
    requires isBetterSol(x,s1,s2) && isBetterSol(x,s2,s3)
    ensures isBetterSol(x,s1,s3)

    lemma isBetterSolRefl(x:Input, s:Solution)
    requires isValidInput(x)
    requires isSolution(x,s)
    ensures isBetterSol(x,s,s)

    predicate isSolGreedy(x:Input, s:Solution)
    requires isValidInput(x)
    requires isSolution(x,s)

    predicate isSolOptimal(x:Input, s:Solution)
    requires isValidInput(x)
    requires isSolution(x,s)
    {
      forall sol | isSolution(x,sol) :: isBetterSol(x,s,sol)
    }

    lemma betterThanOptimal(x:Input, s:Solution, optimalS:Solution)
    requires isValidInput(x)
    requires isSolution(x,s) && isSolution(x,optimalS)
    requires isSolOptimal(x,optimalS) && isBetterSol(x,s,optimalS)
    ensures isSolOptimal(x,s)
    {
      forall s' | isSolution(x,s') ensures isBetterSol(x,s,s')
      {
        assert isBetterSol(x, s, optimalS);
        assert isBetterSol(x, optimalS, s');
        isBetterSolTrans(x, s,optimalS, s');
      }
    }

    // ------- 2. ALGORITHM -------

    method greedy(x:InputA) returns (res:OutputA)
    requires x.Valid() 
    requires isValidInput(inputTrans(x))
    ensures res.Valid(x)
    ensures isSolution(inputTrans(x),outputTrans(x,res))
    ensures isSolGreedy(inputTrans(x),outputTrans(x,res))

    method algorithm(x:InputA) returns (res:OutputA)
    requires x.Valid() 
    requires isValidInput(inputTrans(x))
    ensures res.Valid(x)
    ensures isSolution(inputTrans(x),outputTrans(x,res))
    ensures isSolOptimal(inputTrans(x),outputTrans(x,res))
    {
      ghost var inputTr := inputTrans(x);
      res := greedy(x);
      assert inputTrans(x)==old(inputTrans(x));
      existsOptimalSolution(inputTr);

      ghost var sol :| isSolution(inputTr, sol) && isSolOptimal(inputTr, sol);
      reduction(inputTr, outputTrans(x,res),sol);      
    }

    lemma existsOptimalSolution(x:Input)
    requires isValidInput(x)
    ensures exists sol :: isSolution(x,sol) && isSolOptimal(x,sol)

    // ------- 3. VERIFICATION -------

    ghost method reduction(x:Input, greedy:Solution, optimal:Solution) 
    requires isValidInput(x)
    requires isSolution(x, greedy) && isSolution(x, optimal)
    requires isSolGreedy(x, greedy) && isSolOptimal(x, optimal)
    ensures isBetterSol(x, greedy, optimal)
    ensures isSolOptimal(x, greedy)
    {
      var i := 0; var optimal':=optimal;
      isBetterSolRefl(x, optimal');

      while (i < |greedy| && i < |optimal'|)
        invariant 0 <= i <= |optimal'|
        invariant 0 <= i <= |greedy|
        invariant isSolution(x, optimal')
        invariant isSolOptimal(x,optimal')
        invariant isBetterSol(x, optimal', optimal)
        invariant optimal'[..i] == greedy[..i]
        {
          if (greedy[i] != optimal'[i])
            {
              ghost var oldOptimal := optimal';
              optimal' := reduction_step(x, greedy, optimal', i);
              betterThanOptimal(x, optimal', oldOptimal);
              isBetterSolTrans(x,optimal',oldOptimal,optimal);
            }
          i := i+1;
        }

      ghost var oldOptimal := optimal';
      optimal' := endReduction(x,greedy,optimal');
      isBetterSolTrans(x,optimal',oldOptimal,optimal);
      betterThanOptimal(x, greedy, optimal);
    }

    ghost method endReduction(x:Input, greedy:Solution, optimal:Solution) returns (optimal':Solution)
    requires isValidInput(x)
    requires isSolution(x,greedy) && isSolution(x,optimal)
    requires isSolGreedy(x,greedy) && isSolOptimal(x,optimal)
    requires |optimal| <= |greedy| ==> optimal[..|optimal|] == greedy[..|optimal|]
    requires |optimal| > |greedy| ==> optimal[..|greedy|] == greedy[..|greedy|]
    ensures isSolution(x,optimal')
    ensures isBetterSol(x, optimal', optimal)
    ensures optimal' == greedy

    ghost method reduction_step(x:Input, greedy:Solution, optimal:Solution, i:nat) returns (optimal':Solution)
    requires isValidInput(x)
    requires isSolution(x, greedy) && isSolution(x, optimal)
    requires isSolGreedy(x, greedy) && isSolOptimal(x, optimal)
    requires 0 <= i < |greedy| && 0 <= i < |optimal|
    requires greedy[i] != optimal[i] && greedy[0..i] == optimal[0..i]
    ensures isSolution(x, optimal')
    ensures isBetterSol(x, optimal', optimal)
    ensures |optimal| == |optimal'|
    ensures optimal'[0..i+1] == greedy[0..i+1]
}