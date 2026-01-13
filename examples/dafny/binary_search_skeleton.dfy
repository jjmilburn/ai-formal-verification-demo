// Binary Search - Skeleton for LLM to annotate
// The implementation is correct, but missing verification annotations.
// Task: Add requires, ensures, and loop invariants to make this verify.

method BinarySearch(a: array<int>, key: int) returns (index: int)
  // TODO: Add precondition - array must be sorted
  // TODO: Add postcondition - if index >= 0, then a[index] == key
  // TODO: Add postcondition - if index < 0, key is not in array
{
  var lo := 0;
  var hi := a.Length;

  while lo < hi
    // TODO: Add loop invariants
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else if a[mid] > key {
      hi := mid;
    } else {
      return mid;
    }
  }

  return -1;
}
