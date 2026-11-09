function SumDivs(n: nat, d: nat): nat
  decreases d
{
  if d == 0 then 0
  else (if n % d == 0 then d else 0) + SumDivs(n, d - 1)
}

method FindOddPerfect() returns (n: nat)
  ensures n % 2 == 0 && n > 1 && SumDivs(n, n - 1) == n
  decreases *
{
  n := 2;
  while SumDivs(n, n - 1) != n
    invariant n % 2 == 0 && n >= 2
    decreases *
  {
    n := n + 2;
  }
}