// Max Array - Fully Verified Implementation
// Find the maximum element in a non-empty array

method FindMax(a: array<int>) returns (max: int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
  ensures exists i :: 0 <= i < a.Length && a[i] == max
{
  max := a[0];
  var idx := 1;

  while idx < a.Length
    invariant 1 <= idx <= a.Length
    invariant forall i :: 0 <= i < idx ==> a[i] <= max
    invariant exists i :: 0 <= i < idx && a[i] == max
  {
    if a[idx] > max {
      max := a[idx];
    }
    idx := idx + 1;
  }
}
