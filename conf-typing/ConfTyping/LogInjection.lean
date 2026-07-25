/-
  A third real sink — brick 29: log injection / log forging (CWE-117).

  Bricks 17, 27 established that brick 14's "make a channel real" method is not
  injection-specific — path traversal and OS command injection are the same
  data-not-structure discipline over different metacharacters. This brick adds a
  fourth channel with yet another metacharacter: **log injection** (CWE-117),
  where an untrusted value containing a **record separator** (a newline) forges
  an extra log record.

  A log is tokenized into records by splitting on the newline: `n` separators
  give `n+1` records. As with the other sinks, the *executed structure* is the
  even (structural) records — the genuine log entries — and an intended field
  lives in a data record. LogStr forging is precisely **an untrusted value changing
  that structure**: a newline inside the value opens a new record, so an attacker
  writes a forged entry (e.g. a fake "login succeeded" line).

  Two ways to build a log entry from a trusted preamble and an untrusted field:
  * **concatenation** splices the field as raw text and re-splits the whole log
    — so a newline inside the field forges a record (`log_concat_injectable`);
  * **structured logging** binds the field as one opaque record whose newlines
    are never interpreted as separators — so the structure is a function of the
    preamble alone (`field_immune`), and for benign fields the two agree
    (`field_correct`).

  Integrity noninterference with a real log sink: the executed structure must not
  depend on the untrusted field. Structured logging satisfies it
  (`field_noninterference`); concatenation does not (`log_concat_leaks`). Same
  discipline as SQL injection, path traversal, and command injection — data must
  not become structure — now for a fourth channel.
-/
import ConfTyping.InjectionReal

namespace ConfTyping

/-! ## Characters, logs, and the record splitter -/

/-- A log character: the record separator (a newline), or an ordinary character. -/
inductive GCh where
  | nl : GCh           -- the record separator (newline)
  | c  : Nat → GCh     -- an ordinary character
deriving DecidableEq

abbrev LogStr := List GCh

/-- Does the string contain a newline? -/
def hasNL : LogStr → Bool
  | [] => false
  | .nl :: _ => true
  | .c _ :: r => hasNL r

/-- Split a log into its records on newlines: `recordsOf` returns the maximal
    newline-free runs, so `n` separators give `n+1` records. -/
def recordsOf : LogStr → List LogStr
  | [] => [[]]
  | .nl :: r => [] :: recordsOf r
  | .c n :: r =>
      match recordsOf r with
      | a :: as => (.c n :: a) :: as
      | []      => [[.c n]]

/-- The even-indexed records (positions 0, 2, 4, …) — the structural ones. -/
def levens : List LogStr → List LogStr
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: levens xs

/-- The **executed structure**: the structural log records. Injection = the
    untrusted field changing this. -/
def logSkeleton (s : LogStr) : List LogStr := levens (recordsOf s)

/-! ## The two builds -/

/-- **Concatenation build.** Splice the untrusted field `v` after the trusted
    preamble with a separator, then hand the *whole log* to the splitter — the
    injectable one, `log.write(preamble + "\n" + userField)`. -/
def buildLogConcat (pre v : LogStr) : LogStr := pre ++ .nl :: v

/-- **Structured build.** The field is bound as one opaque record; the executed
    structure is the preamble alone, *by construction independent of any newlines
    inside the field*. This models `log.info(event, field=value)`. -/
def fieldParam (pre : LogStr) (_v : LogStr) : List LogStr := [pre]

/-! ## Splitter lemmas -/

theorem recordsOf_ne_nil (s : LogStr) : recordsOf s ≠ [] := by
  cases s with
  | nil => simp [recordsOf]
  | cons ch r =>
      cases ch with
      | nl => simp [recordsOf]
      | c n => simp only [recordsOf]; cases recordsOf r with
        | nil => simp
        | cons _ _ => simp

/-- A newline-free string is a single record. -/
theorem records_nlfree : ∀ {s : LogStr}, hasNL s = false → recordsOf s = [s]
  | [], _ => rfl
  | .nl :: _, h => by simp [hasNL] at h
  | .c n :: r, h => by
      have hr : hasNL r = false := by simpa [hasNL] using h
      simp only [recordsOf, records_nlfree hr]

/-- Splitting after a newline-free prefix: `recordsOf (a ++ nl·b) = a :: recordsOf b`. -/
theorem records_append_nl : ∀ {a : LogStr}, hasNL a = false → ∀ b : LogStr,
    recordsOf (a ++ .nl :: b) = a :: recordsOf b
  | [], _, b => rfl
  | .nl :: _, h, _ => by simp [hasNL] at h
  | .c n :: a', h, b => by
      have hr : hasNL a' = false := by simpa [hasNL] using h
      simp only [List.cons_append, recordsOf, records_append_nl hr b]

/-! ## Structured logging is injection-safe -/

/-- **Structured logging is immune to injection.** The executed structure does
    not depend on the untrusted field — true *by construction*, because the field
    is never re-split. -/
theorem field_immune (pre v v' : LogStr) :
    fieldParam pre v = fieldParam pre v' := rfl

/-- **Structured logging computes the right log.** For a well-behaved
    (newline-free) field and preamble, the bound structure equals what a correct
    split of the concatenated log would produce — faithful, and immune when the
    field is adversarial. -/
theorem field_correct {pre v : LogStr}
    (hpre : hasNL pre = false) (hv : hasNL v = false) :
    logSkeleton (buildLogConcat pre v) = fieldParam pre v := by
  have h1 : recordsOf (buildLogConcat pre v) = [pre, v] := by
    show recordsOf (pre ++ .nl :: v) = [pre, v]
    rw [records_append_nl hpre v, records_nlfree hv]
  simp only [logSkeleton, h1, levens, fieldParam]

/-- **Structured logging satisfies integrity noninterference.** The executed log
    structure is invariant under any change to the untrusted field. -/
theorem field_noninterference (pre : LogStr) :
    ∀ v v', fieldParam pre v = fieldParam pre v' :=
  fun v v' => field_immune pre v v'

/-! ## Concatenation is injectable -/

/-- Witness data: a benign field, and a forging payload `x ⏎ y` (a newline that
    opens a new record, then forged log text). -/
def lBenign : LogStr := [.c 0]
def lPayload : LogStr := [.c 3, .nl, .c 4]   -- newline forges a second record
def lPre : LogStr := [.c 1]

/-- **Concatenation is injectable.** With the same trusted preamble, a benign
    field and a payload with a newline produce *different executed structures* —
    the payload's text lands in a new structural record. LogStr forging as a
    theorem. -/
theorem log_concat_injectable :
    logSkeleton (buildLogConcat lPre lBenign) ≠ logSkeleton (buildLogConcat lPre lPayload) := by
  decide

/-- The benign field yields the intended structure (just the preamble) — the
    injection is the *difference*, not mere nonequality. -/
theorem log_benign_correct : logSkeleton (buildLogConcat lPre lBenign) = [lPre] := by
  decide

/-! ## Integrity noninterference, with a real log sink

    Two runs share the trusted preamble but may differ on the untrusted field.
    LogStr-injection-freedom is: the executed structure is the same — integrity
    noninterference, over a real log construction. -/

/-- **Concatenation violates integrity noninterference.** Some trusted preamble
    and two untrusted fields give different executed structures — the untrusted
    input influences the trusted sink, exactly the CWE-117 leak. -/
theorem log_concat_leaks :
    ∃ (pre v v' : LogStr),
      logSkeleton (buildLogConcat pre v) ≠ logSkeleton (buildLogConcat pre v') :=
  ⟨lPre, lBenign, lPayload, log_concat_injectable⟩

/-- **The by-construction fix, as integrity NI.** Structured logging makes the
    executed structure a constant function of the untrusted field (High-invariant),
    i.e. it satisfies the taint form of injection-freedom T1 identifies as the
    unique admissible 2-safety formulation — here on a real log. The sink factors
    through the trusted preamble alone. -/
theorem field_sink_trusted (pre : LogStr) :
    ∃ f : Unit → List LogStr, ∀ v, fieldParam pre v = f () :=
  ⟨fun _ => [pre], fun _ => rfl⟩

end ConfTyping
