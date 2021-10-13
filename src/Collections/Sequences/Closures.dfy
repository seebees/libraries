include "../../Wrappers.dfy"

module Closures {

  import opened Wrappers

  trait {:termination false} Action<A, R> {
    method Invoke(a: A) returns (r: R) // modifies InvokeRepr(a)
    // function method InvokeRepr(a: A): set<object>
  }

  trait {:termination false} ActionWithResult<A, R, E> extends Action<A, Result<R, E>> {
    method Invoke(a: A) returns (r: Result<R, E>) // modifies InvokeRepr(a)
    // function method InvokeRepr(a: A): set<object>
  }

  method Map<A, R>(
    s: seq<A>,
    action: Action<A, R>
  )
    returns (res: seq<R>)
    // modifies set x | exists a | a in s :: x in action.InvokeRepr(a)
  {
    var rs := [];
    for i := 0 to |s| {
      var r := action.Invoke(s[i]);
      rs := rs + [r];
    }
    return rs;
  }

  method MapWithResult<A, R, E>(
    s: seq<A>,
    action: ActionWithResult<A, R, E>
  )
    returns (res: Result<seq<R>, E>)
    // modifies set x | exists a | a in s :: x in action.InvokeRepr(a)
  {
    var rs := [];
    for i := 0 to |s| {
      var r :- action.Invoke(s[i]);
      rs := rs + [r];
    }
    return Success(rs);
  }

  method Filter<A>(
    s: seq<A>,
    action: Action<A, bool>
  )
    returns (res: seq<A>)
  // modifies set x | exists a | a in s :: x in action.InvokeRepr(a)
  {
    var rs := [];
    for i := 0 to |s| {
      var r := action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return rs;
  }


  method FilterWithResult<A, E>(
    s: seq<A>,
    action: ActionWithResult<A, bool, E>
  )
    returns (res: Result<seq<A>, E>)
  // modifies set x | exists a | a in s :: x in action.InvokeRepr(a)
  {
    var rs := [];
    for i := 0 to |s| {
      var r :- action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return Success(rs);
  }

  method ReduceToSuccess<A, B, E>(
    s: seq<A>,
    action: ActionWithResult<A, B, E>
  )
    returns (res: Result<B, seq<E>>)
  {
    var errors := [];
    for i := 0 to |s| {
      var attempt := action.Invoke(s[i]);
      if attempt.Success? {
        return Success(attempt.value);
      } else {
        errors := errors + [attempt.error];
      }
    }
    return Failure(errors);
  }
}
