// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

include "../../Relations.dfy"

module {:options "-functionSyntax:4"} Seq.MergeSort {

  import opened Relations

  //Splits a sequence in two, sorts the two subsequences using itself, and merge the two sorted sequences using `MergeSortedWith`
  function {:isolate_assertions} {:only} MergeSortBy<T(!new)>(a: seq<T>, lessThanOrEq: (T, T) -> bool): (result :seq<T>)
    requires TotalOrdering(lessThanOrEq)
    ensures multiset(a) == multiset(result)
    ensures SortedBy(result, lessThanOrEq)
  {
    if |a| <= 1 then
      a
    else
      var splitIndex := |a| / 2;
      var left, right := a[..splitIndex], a[splitIndex..];

      assert a == left + right;

      var leftSorted := MergeSortBy(left, lessThanOrEq);
      var rightSorted := MergeSortBy(right, lessThanOrEq);

      MergeSortedWith(leftSorted, rightSorted, lessThanOrEq)
  }
  // by method {
  //   if |a| <= 1 {
  //     return a;
  //   } else {
  //     var tmp := new T[|a|](i requires 0 <= i < |a| => a[i]);
  //     MSort(tmp, lessThanOrEq);
  //     return tmp[..];
  //   }
  // }

  function {:only} Bar<T(!new)>(a: seq<T>, lessThanOrEq: (T, T) -> bool): (result :seq<T>)
    requires TotalOrdering(lessThanOrEq)
  {
    MergeSortBy(a, lessThanOrEq)
  }
  by method {
    if |a| <= 1 {
      return a;
    } else {
      
      var tmp := new T[|a|](i requires 0 <= i < |a| => a[i]);
      MSort(tmp, lessThanOrEq);

      
      ghost var other := MergeSortBy(a, lessThanOrEq);
      
      calc {
        multiset(tmp[..]);
      ==
        multiset(a);
      ==
        multiset(other);
      }

      assume false;

      assert multiset(tmp[..]) == multiset(other);

      assume false;

      Foo(tmp[..], MergeSortBy(a, lessThanOrEq), lessThanOrEq);
      return tmp[..];
    }
  }


  lemma Foo<T(!new)>(s1: seq<T>, s2: seq<T>, lessThanOrEq: (T, T) -> bool)
    requires TotalOrdering(lessThanOrEq)
    requires SortedBy(s1, lessThanOrEq) && SortedBy(s2, lessThanOrEq)
    requires multiset(s1) == multiset(s2)
    ensures s1 == s2




  function {:tailrecursion} MergeSortedWith<T(!new)>(left: seq<T>, right: seq<T>, lessThanOrEq: (T, T) -> bool) : (result :seq<T>)
    requires SortedBy(left, lessThanOrEq)
    requires SortedBy(right, lessThanOrEq)
    requires TotalOrdering(lessThanOrEq)
    ensures multiset(left + right) == multiset(result)
    ensures SortedBy(result, lessThanOrEq)
  {
    if |left| == 0 then
      right
    else if |right| == 0 then
      left
    else if lessThanOrEq(left[0], right[0]) then
      LemmaNewFirstElementStillSortedBy(left[0], MergeSortedWith(left[1..], right, lessThanOrEq), lessThanOrEq);
      assert left == [left[0]] + left[1..];

      [left[0]] + MergeSortedWith(left[1..], right, lessThanOrEq)

    else
      LemmaNewFirstElementStillSortedBy(right[0], MergeSortedWith(left, right[1..], lessThanOrEq), lessThanOrEq);
      assert right == [right[0]] + right[1..];

      [right[0]] + MergeSortedWith(left, right[1..], lessThanOrEq)
  }

  method {:isolate_assertions} MSort<T(!new)>(a: array<T>, lessThanOrEq: (T, T) -> bool, lo: nat := 0, hi: nat := a.Length)
    requires 0 <= lo < hi <= a.Length
    requires TotalOrdering(lessThanOrEq)
    decreases hi - lo
    reads a
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(a[lo..hi], lessThanOrEq)
    ensures a[0..lo] == old(a[0..lo])
    ensures a[hi..] == old(a[hi..])
    ensures a[lo..hi] == MergeSortBy(old(a[lo..hi]), lessThanOrEq)
  {
    var mid := lo + (hi - lo)/2;
    if lo < mid {
      MSort(a, lessThanOrEq, lo, mid);
      MSort(a, lessThanOrEq, mid, hi);

      Merge(a, lessThanOrEq, lo, mid, hi);
    }
  }

  method {:isolate_assertions} Merge<T(!new)>(a: array<T>, lessThanOrEq: (T, T) -> bool, lo: nat, mid:nat, hi: nat)
    requires TotalOrdering(lessThanOrEq)
    requires 0 <= lo < mid <= hi <= a.Length
    requires SortedBy(a[lo..mid], lessThanOrEq)
    requires SortedBy(a[mid..hi], lessThanOrEq)
    reads a
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures SortedBy(a[lo..hi], lessThanOrEq)
    ensures a[0..lo] == old(a[0..lo])
    ensures a[hi..] == old(a[hi..])
    // ensures a[lo..hi] == MergeSortedWith(old(a[lo..mid]), old(a[mid..hi]), lessThanOrEq)
    ensures MergeSortBy(old(a[lo..hi]), lessThanOrEq) == a[lo..hi]
  {
    var fill := i requires 0 <= i < a.Length reads a => a[i];
    var left, right :=
      new T[mid - lo](i requires 0 <= i < a.Length - lo reads a  => a[lo + i]),
      new T[hi - mid](i requires 0 <= i < a.Length - mid reads a => a[mid + i]);

    var i, l, r := lo,0,0;

    label BEFORE_LOOP:

    assert a[lo..mid] == left[..];
    assert a[mid..hi] == right[..];

    assert a[..i] + left[l..] + right[r..] + a[hi..] == a[..] == old(a[..]);

    while i < hi
      decreases hi - i
      modifies a

      invariant 0 <= lo <= i <= hi <= a.Length
      invariant 0 <= l <= left.Length
      invariant 0 <= r <= right.Length

      invariant
        && lo < i
        && r < right.Length
        ==>
          && lessThanOrEq(a[i-1], right[r])

      invariant
        && lo < i
        && l < left.Length
        ==>
          && lessThanOrEq(a[i-1], left[l])

      invariant SortedBy(a[lo..i], lessThanOrEq)

      invariant unchanged@BEFORE_LOOP(left)
      invariant unchanged@BEFORE_LOOP(right)
      invariant SortedBy(left[..], lessThanOrEq)
      invariant SortedBy(right[..], lessThanOrEq)

      invariant lo + l + r == i

      invariant a[0..lo] == old(a[0..lo])
      invariant a[i..] == old(a[i..])
      invariant multiset(a[..i] + left[l..] + right[r..] + a[hi..]) == multiset(old(a[..]))




      // invariant
      //   assert old(a[lo..lo+l]) == left[..l];
      //   a[lo..i] == MergeSortedWith(old(a[lo..lo+l]), old(a[mid..mid+r]), lessThanOrEq)

      invariant a[lo..i] == MergeSortedWith(left[..l], right[..r], lessThanOrEq)

    {

      if l < left.Length && r < right.Length {
        if lessThanOrEq(left[l], right[r]) {
          a[i] := left[l];

          PushStillSortedBy(a, lo, i, lessThanOrEq);
          l := l + 1;

          assert l < left.Length ==> lessThanOrEq(a[i], left[l]) by {
            assert a[i] == left[l-1];
            if l < left.Length {
              assert lessThanOrEq(left[l-1], left[l]) by {
                assert forall i, j | 0 <= i < j < |left[..]| :: lessThanOrEq(left[..][i], left[..][j]);
                assert 0 <= l-1 < l < |left[..]|;
              }
            }
          }
          assert lessThanOrEq(a[i], right[r]);

          assert multiset(a[..i+1] + left[l..] + right[r..] + a[hi..]) == multiset(old(a[..])) by {
            calc {
              a[..i] + left[l-1..] + right[r..] + a[hi..];
            == {assert [left[l-1]] + left[l..] == left[l-1..];}
              a[..i] + ([left[l-1]] + left[l..]) + right[r..] + a[hi..];
            == {assert a[i] == left[l-1];}
              a[..i] + ([a[i]] + left[l..]) + right[r..] + a[hi..];
            == {assert a[..i] + ([a[i]] + left[l..]) == (a[..i] + [a[i]]) + left[l..];}
              (a[..i] + [a[i]]) + left[l..] + right[r..] + a[hi..];
            == {assert a[..i] +[a[i]] == a[..i+1];}
              a[..i+1] + left[l..] + right[r..] + a[hi..];
            }
          }

        } else {
          a[i] := right[r];

          PushStillSortedBy(a, lo, i, lessThanOrEq);
          r := r + 1;

          assert r < right.Length ==> lessThanOrEq(a[i], right[r]) by {
            assert a[i] == right[r-1];
            if r < right.Length {
              assert lessThanOrEq(right[r-1], right[r]) by {
                assert forall i, j | 0 <= i < j < |right[..]| :: lessThanOrEq(right[..][i], right[..][j]);
                assert 0 <= r-1 < r < |right[..]|;
              }
            }
          }
          assert lessThanOrEq(a[i], left[l]);

          assert multiset(a[..i+1] + left[l..] + right[r..] + a[hi..]) == multiset(old(a[..])) by {
            calc {
              a[..i] + left[l..] + right[r-1..] + a[hi..];
            == {assert [right[r-1]] + right[r..] == right[r-1..];}
              a[..i] + left[l..] + ([right[r-1]] + right[r..]) + a[hi..];
            == {assert a[i] == right[r-1];}
              a[..i] + left[l..] + ([a[i]] + right[r..]) + a[hi..];
            }
          }
        }

      } else if l == left.Length && r < right.Length {
        // We reached the end of left,
        // all of right is in order,
        // we just need to move it in.
        a[i] := right[r];

        PushStillSortedBy(a, lo, i, lessThanOrEq);
        r := r + 1;

        assert r < right.Length ==> lessThanOrEq(a[i], right[r]);

        assert multiset(a[..i+1] + left[l..] + right[r..] + a[hi..]) == multiset(old(a[..])) by {
          calc {
            a[..i] + left[l..] + right[r-1..] + a[hi..];
          == {assert [right[r-1]] + right[r..] == right[r-1..];}
            a[..i] + left[l..] + ([right[r-1]] + right[r..]) + a[hi..];
          == {assert a[i] == right[r-1];}
            a[..i] + left[l..] + ([a[i]] + right[r..]) + a[hi..];
          }
        }

      } else if r == right.Length && l < left.Length {
        // We reached the end of right
        // all of left is in order,
        // we just need to move it in.
        a[i] := left[l];

        PushStillSortedBy(a, lo, i, lessThanOrEq);
        l := l + 1;

        assert l < left.Length ==> lessThanOrEq(a[i], left[l]) by {
          assert a[i] == left[l-1];
        }

        assert multiset(a[..i+1] + left[l..] + right[r..] + a[hi..]) == multiset(old(a[..])) by {
          calc {
            a[..i] + left[l-1..] + right[r..] + a[hi..];
          == {assert [left[l-1]] + left[l..] == left[l-1..];}
            a[..i] + ([left[l-1]] + left[l..]) + right[r..] + a[hi..];
          == {assert a[i] == left[l-1];}
            a[..i] + ([a[i]] + left[l..]) + right[r..] + a[hi..];
          == {assert a[..i] + ([a[i]] + left[l..]) == (a[..i] + [a[i]]) + left[l..];}
            (a[..i] + [a[i]]) + left[l..] + right[r..] + a[hi..];
          == {assert a[..i] +[a[i]] == a[..i+1];}
            a[..i+1] + left[l..] + right[r..] + a[hi..];
          }
        }
      } else {
        // There is never a case where
        // we are not pulling from right or left
        assert false;
      }

      i := i + 1;

      assert a[i..] == old(a[i..]);
    }

    assert multiset(a[..]) == multiset(old(a[..])) by {
      assert multiset(a[..i] + left[l..] + right[r..] + a[hi..]) == multiset(old(a[..]));
      assert a[..] == a[..i] + left[l..] + right[r..] + a[hi..];
    }

  }

  lemma PushStillSortedBy<T(!new)>(a: array<T>, lo:nat, i: nat, lessThan: (T, T) -> bool)
    requires 0 <= lo <= i < a.Length
    requires SortedBy(a[lo..i], lessThan)
    requires |a[lo..i]| == 0 || lessThan(a[lo..i][|a[lo..i]| - 1], a[i])
    requires TotalOrdering(lessThan)
    ensures SortedBy(a[lo..i + 1], lessThan)
    ensures lo < i ==> lessThan(a[i - 1], a[i])
  {}

  method ToArray<T(!new)>(xs: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |xs|
    ensures forall i :: 0 <= i < |xs| ==> a[i] == xs[i]
  {
    a := new T[|xs|](i requires 0 <= i < |xs| => xs[i]);
  }
}
