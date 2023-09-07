

trait Event {
  const source: object
}

class SampleEvent extends Event {
  constructor(source: object) 
  {
    this.source := source;
  }
}

class {:separated} History {

  var events: seq<Event>

  constructor()
    ensures events == []
  {
    events := [];
  }

  twostate predicate Invariant()
    reads this
  {
    && old(events) <= events
    // We'd also like to be able to say this kind of thing
    // ONLY when assuming the post-condition of methods...
    // && var others := events[|old(events)|..];
    // && forall other <- others :: other.source != <my source>
  }

  method AddEvent(e: Event)
    modifies this
    ensures Invariant()

    // Sequential version - will verify against the body of the method,
    // but not be true in concurrent mode.
    // ensures events == old(events) + [e]

    // This is the weakened form that clients assume externally instead.
    // Follows from the combination of the sequential ensures plus the twostate invariant.
    ensures exists others :: events == old(events) + [e] + others
  {
    events := events + [e];
    assert events == old(events) + [e] + [];
  }
}

class ThreadID {
  constructor() {
  }
}

method HistoryClient() {
  var history := new History();
  var source := new ThreadID();

  var event := new SampleEvent(source);
  history.AddEvent(event);

  assert event in history.events;

  // This is what we want, but can't yet prove.
  // Can we somehow express in the Invariant that the other events
  // (which other concurrent executions may have added in this context)
  // cannot have the same source?
  // Could we support an invariant which is interpreted slightly differently
  // between the contexts of ensuring it on a class method
  // vs. assuming it after an external call to that method?
  assert |set e <- history.events :: e.source == source| == 1; // Error: assertion might not hold
}