// Max Array - Skeleton for LLM to annotate
// Find the maximum element in a non-empty array

method FindMax(a: array<int>) returns (max: int)
  // TODO: Add precondition - array must be non-empty
  // TODO: Add postcondition - max is >= all elements
  // TODO: Add postcondition - max exists in the array
{
  max := a[0];
  var idx := 1;

  while idx < a.Length
    // TODO: Add loop invariants
  {
    if a[idx] > max {
      max := a[idx];
    }
    idx := idx + 1;
  }
}
