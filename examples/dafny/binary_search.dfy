// Binary Search - Fully Verified Implementation
// This is the target: what a correctly annotated version looks like

method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]  // sorted
  ensures index >= 0 ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
  var lo := 0;
  var hi := a.Length;

  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> a[i] > key
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

// Simple test method
method Main() {
  var a := new int[5][1, 3, 5, 7, 9];
  var idx := BinarySearch(a, 5);
  print "Found 5 at index: ", idx, "\n";

  idx := BinarySearch(a, 4);
  print "Found 4 at index: ", idx, " (should be -1)\n";
}
