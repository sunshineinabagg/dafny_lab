method SumTo(n: nat) returns (s: nat)
  ensures 2 * s == n * (n + 1)
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 2 * s == i * (i + 1)
  {
    i := i + 1;
    s := s + i;
  }
}