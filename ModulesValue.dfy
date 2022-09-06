include "./Modules.dfy"

abstract module GreedyAlgorithmValue refines GreedyAlgorithm {

    function solutionValue(x: Input, s: Solution): nat
    requires isValidInput(x)
    requires isSolution(x, s)

    predicate isBetterSol(x:Input, s1:Solution, s2:Solution)
    {
      solutionValue(x, s1) <= solutionValue(x, s2)
    }

    lemma isBetterSolTrans(x:Input, s1:Solution, s2:Solution, s3:Solution)
    {}

    lemma isBetterSolRefl(x:Input, s:Solution)
    {}

    lemma existsSolution(x: Input)
    requires isValidInput(x)
    ensures exists sol :: isSolution(x, sol)

    lemma existsOptimalSolution(x:Input)
    {
      existsSolution(x);
      var currentSol :| isSolution(x, currentSol);
      var value := solutionValue(x, currentSol);

      while (!isSolOptimal(x, currentSol))
        invariant isSolution(x, currentSol)
        invariant value == solutionValue(x, currentSol)
        decreases value
        {
          var betterSol :| isSolution(x, betterSol) && !isBetterSol(x, currentSol, betterSol);
          assert solutionValue(x, currentSol) > solutionValue(x, betterSol);
          currentSol := betterSol;
          value := solutionValue(x, betterSol);
        }
      assert isSolution(x, currentSol) && isSolOptimal(x, currentSol);
    }
}

