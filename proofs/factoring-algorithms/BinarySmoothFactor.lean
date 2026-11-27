import Std

/-!
# Binary trial division with a finite-alphabet running-time bound

This file runs with Lean 4.19.0 and its standard library. Check it with
`lean BinarySmoothFactor.lean`. For example, `#eval BinarySmoothFactor.factor 72`
returns `[3, 3, 2, 2, 2]`.

* `factor_correct` proves that the factors of every n ≥ 2 are prime and have
  product n. A repeated prime appears once per occurrence.
* `factor_smooth` bounds the cost of the binary machine by
  (B + b) · 12(b + 1)² + 3(b + 1) transitions when its b-bit input has no
  prime factor larger than B. The machine receives only the input digits.
* `polynomial_on_smooth` specializes this to B = b^e. The theorem counts
  every transition through the final output, including binary arithmetic.
* `exceeds_every_polynomial` proves that arbitrarily large prime squares
  exceed every fixed polynomial time budget for this machine.

The input is most-significant-bit first. The machine tests the divisors
2, 3, ... in order, retaining a divisor after a successful division. Division
uses a one-bit full subtractor. Every transition consults a bounded number of
cells of fixed finite alphabets. The output uses a b-bit binary field and a
separator for each prime factor. Reading the output stack from its top gives
the factors in descending order. The integer interface decodes those fields.
All bounds concern transitions of this binary machine. The cost of running the
Lean evaluator on a particular computer is a separate implementation detail.
-/

namespace BinarySmoothFactor

local macro "poly" : tactic => `(tactic|
  (simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.one_mul, Nat.mul_one,
    Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] <;> omega))

abbrev Word := List Bool

def digit : Bool → Nat | false => 0 | true => 1

/-- Interpret a word least significant bit first. -/
def little : Word → Nat
  | [] => 0
  | x :: xs => digit x + 2 * little xs

/-- Interpret a word most significant bit first. -/
def big : Word → Nat
  | [] => 0
  | x :: xs => 2^xs.length * digit x + big xs

private theorem digit_le (x : Bool) : digit x ≤ 1 := by cases x <;> decide

theorem big_lt (w : Word) : big w < 2^w.length := by
  induction w with
  | nil => decide
  | cons x xs ih =>
    cases x <;> simp only [big, digit, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
      List.length_cons, Nat.pow_succ] <;> omega

theorem little_lt (w : Word) : little w < 2^w.length := by
  induction w with
  | nil => decide
  | cons x xs ih =>
    have := digit_le x
    simp only [little, List.length_cons, Nat.pow_succ]
    omega

inductive Mark where
  | bit (x : Bool)
  | sep
  deriving Repr, DecidableEq

/-- Decode a stack of binary factor records. Each record has a separator. -/
def decode : List Mark → Nat → List Nat
  | [], _ => []
  | .bit b :: xs, a => decode xs (2*a + digit b)
  | .sep :: xs, a => a :: decode xs 0

private def packet (d : Word) (out : List Mark) :=
  (d.map Mark.bit).reverse ++ .sep :: out

private theorem decode_bits (w : Word) (tail : List Mark) (a : Nat) :
    decode ((w.map Mark.bit).reverse ++ tail) a =
      decode tail (2^w.length*a + little w) := by
  induction w generalizing tail with
  | nil => simp [little]
  | cons x xs ih =>
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, List.length_cons, Nat.pow_succ, little]
    rw [ih]
    simp only [decode]
    congr 1
    poly

private theorem decode_packet (d : Word) (out : List Mark) :
    decode (packet d out) 0 = little d :: decode out 0 := by
  simp [packet, decode_bits, decode]

private def diff (x y borrow : Bool) := (x ^^ y) ^^ borrow
private def borrowOut (x y borrow : Bool) := (!x && (y || borrow)) || (y && borrow)

private theorem full_subtractor (x y b : Bool) :
    digit x + 2*digit (borrowOut x y b) =
    digit y + digit b + digit (diff x y b) := by
  cases x <;> cases y <;> cases b <;> decide

structure Cell where
  divisor : Bool
  original : Bool
  difference : Bool
  deriving Repr

structure Tape where
  unread : Word
  /-- Dividend and quotient digits, newest first. -/
  seen : List (Bool × Bool)
  deriving Repr

inductive Phase where
  | boot (input backwards zeros : Word)
  | home (backwards input divisor : Word)
  | start (input divisor : Word)
  | zeros (input divisor backwards remainder : Word)
  | rewind (input backwards divisor remainder : Word)
  | feed (t : Tape) (divisor remainder : Word)
  | subtract (t : Tape) (inputBit : Bool) (divisor shifted : Word)
      (cells : List Cell) (borrow : Bool)
  | restore (t : Tape) (inputBit quotientBit : Bool) (cells : List Cell)
      (divisor remainder : Word)
  | test (seen : List (Bool × Bool)) (divisor remainder : Word) (exact : Bool)
  | reload (exact : Bool) (seen : List (Bool × Bool)) (input divisor : Word)
  | emit (input divisor backwards : Word)
  | increment (input divisor backwards : Word) (carry : Bool)
  | replace (input backwards divisor : Word)
  | halt
  deriving Repr

abbrev State := Phase × List Mark

/-- One finite-control transition. Each stack alphabet is finite. Only a
constant number of top cells are inspected, pushed, or popped in each case.
The output stack grows by at most one symbol per transition. -/
def step : State → State
  | (.boot (x::xs) rev zs, o) => (.boot xs (x::rev) (false::zs), o)
  | (.boot [] rev (_::_::zs), o) => (.home rev [] (false::true::zs), o)
  | (.boot [] _ _, o) => (.halt, o)
  | (.home (x::xs) w d, o) => (.home xs (x::w) d, o)
  | (.home [] w d, o) => (.start w d, o)
  | (.start (false::xs) d, o) => (.start xs d, o)
  | (.start (true::x::xs) d, o) => (.zeros (true::x::xs) d [] [], o)
  | (.start _ _, o) => (.halt, o)
  | (.zeros w (x::xs) rev r, o) => (.zeros w xs (x::rev) (false::r), o)
  | (.zeros w [] rev r, o) => (.rewind w rev [] r, o)
  | (.rewind w (x::xs) d r, o) => (.rewind w xs (x::d) r, o)
  | (.rewind w [] d r, o) => (.feed ⟨w, []⟩ d r, o)
  | (.feed ⟨x::xs, seen⟩ d r, o) => (.subtract ⟨xs, seen⟩ x d (x::r) [] false, o)
  | (.feed ⟨[], seen⟩ d r, o) => (.test seen d r true, o)
  | (.subtract t a (y::ys) (x::xs) cells b, o) =>
    (.subtract t a ys xs (⟨y,x,diff x y b⟩::cells) (borrowOut x y b), o)
  | (.subtract t a [] [high] cells b, o) => (.restore t a (high || !b) cells [] [], o)
  | (.subtract _ _ _ _ _ _, o) => (.halt, o)
  | (.restore t a take (f::fs) d r, o) =>
    (.restore t a take fs (f.divisor::d) ((if take then f.difference else f.original)::r), o)
  | (.restore t a take [] d r, o) => (.feed ⟨t.unread, (a,take)::t.seen⟩ d r, o)
  | (.test seen d (x::xs) ok, o) => (.test seen d xs (ok && !x), o)
  | (.test seen d [] ok, o) => (.reload ok seen [] d, o)
  | (.reload ok ((a,q)::xs) w d, o) => (.reload ok xs ((if ok then q else a)::w) d, o)
  | (.reload true [] w d, o) => (.emit w d [], .sep::o)
  | (.reload false [] w d, o) => (.increment w d [] true, o)
  | (.emit w (x::xs) rev, o) => (.emit w xs (x::rev), .bit x :: o)
  | (.emit w [] rev, o) => (.replace w rev [], o)
  | (.increment w (x::xs) rev c, o) => (.increment w xs ((x ^^ c)::rev) (x && c), o)
  | (.increment w [] rev _, o) => (.replace w rev [], o)
  | (.replace w (x::xs) d, o) => (.replace w xs (x::d), o)
  | (.replace w [] d, o) => (.start w d, o)
  | (.halt, o) => (.halt, o)

def advance : Nat → State → State
  | 0, s => s
  | k+1, s => advance k (step s)

private theorem advance_add (a b : Nat) (s : State) :
    advance (a+b) s = advance b (advance a s) := by
  induction a generalizing s with
  | zero => simp [advance]
  | succ a ih => simpa only [Nat.succ_add, advance] using ih (step s)

private theorem run_then {s t u : State} {a b : Nat}
    (h : advance a s = t) (j : advance b t = u) : advance (a+b) s = u := by
  rw [advance_add, h, j]

/- A word subtraction records both possible remainders while the sign is
being determined. The final high bit and the borrow select which word to keep. -/
private def frames : Word → Word → Bool → List Cell
  | y::ys, x::xs, b => ⟨y,x,diff x y b⟩ :: frames ys xs (borrowOut x y b)
  | _, _, _ => []

private def lastBorrow : Word → Word → Bool → Bool
  | y::ys, x::xs, b => lastBorrow ys xs (borrowOut x y b)
  | _, _, b => b

private theorem frames_spec (d x : Word) (b : Bool) (h : d.length = x.length) :
    (frames d x b).map Cell.divisor = d ∧
    (frames d x b).map Cell.original = x ∧
    little x + 2^d.length * digit (lastBorrow d x b) =
      little d + digit b + little ((frames d x b).map Cell.difference) := by
  induction d generalizing x b with
  | nil => cases x <;> simp_all [frames, lastBorrow, little]
  | cons y ys ih =>
    cases x with
    | nil => simp at h
    | cons a xs =>
      have ⟨ds, os, arith⟩ := ih xs (borrowOut a y b) (by simpa using h)
      have unit := full_subtractor a y b
      simp only [frames, lastBorrow, List.map_cons, ds, os, true_and, little,
        List.length_cons, Nat.pow_succ]
      rw [Nat.mul_right_comm (2^ys.length) 2]
      omega

private theorem little_append (a b : Word) :
    little (a++b) = little a + 2^a.length * little b := by
  induction a with
  | nil => simp [little]
  | cons x xs ih =>
    simp only [List.cons_append, little, ih, List.length_cons, Nat.pow_succ]
    poly

private theorem select_arith (W D X S : Nat) (hi b : Bool)
    (hs : X + W*digit b = D+S) (hd : D < W) (hr : S < W)
    (bound : X + W*digit hi < 2*D) :
    let q := hi || !b
    X + W*digit hi = D*digit q + (if q then S else X) ∧ (if q then S else X) < D := by
  cases hi <;> cases b <;> simp [digit] at * <;> omega

/-- The fixed-width restore takes the low bits if subtraction underflows and
the low bits of the difference otherwise. The true quotient digit is at most one. -/
private theorem select_digit (d lo : Word) (hi : Bool) (h : d.length = lo.length)
    (range : little (lo++[hi]) < 2 * little d) :
    let fs := frames d lo false
    let take := hi || !lastBorrow d lo false
    let r := if take then fs.map Cell.difference else lo
    little (lo++[hi]) = little d * digit take + little r ∧ little r < little d := by
  obtain ⟨hd, _, sub⟩ := frames_spec d lo false h
  have width : ((frames d lo false).map Cell.difference).length = d.length := by
    simpa using congrArg List.length hd
  have dl := little_lt d
  have sl := little_lt ((frames d lo false).map Cell.difference)
  rw [width] at sl
  have block : little (lo++[hi]) = little lo + 2^d.length * digit hi := by
    simp [little_append,little,h]
  rw [block] at range ⊢
  have ar := select_arith (2^d.length) (little d) (little lo)
    (little ((frames d lo false).map Cell.difference)) hi (lastBorrow d lo false)
    (by simpa [digit] using sub) dl sl range
  cases eq : hi || !lastBorrow d lo false <;> simpa [eq] using ar

private theorem subtract_run (t a hi o) (d lo : Word) (b cells)
    (h : d.length = lo.length) :
    advance (d.length+1) (.subtract t a d (lo++[hi]) cells b, o) =
      (.restore t a (hi || !lastBorrow d lo b) ((frames d lo b).reverse++cells) [] [], o) := by
  induction d generalizing lo b cells with
  | nil => cases lo <;> simp_all [frames,lastBorrow,advance,step]
  | cons y ys ih =>
    cases lo with
    | nil => simp at h
    | cons x xs =>
      simpa [Nat.succ_add, advance, step, frames, lastBorrow, List.reverse_cons, List.append_assoc]
        using ih xs (borrowOut x y b) (⟨y,x,diff x y b⟩::cells) (by simpa using h)

private def pick (take : Bool) (f : Cell) := if take then f.difference else f.original

private theorem restore_run (t a take o) (cells : List Cell) (d r : Word) :
    advance (cells.length+1) (.restore t a take cells d r, o) =
      (.feed ⟨t.unread,(a,take)::t.seen⟩ (cells.reverse.map Cell.divisor++d)
        (cells.reverse.map (pick take)++r), o) := by
  induction cells generalizing d r with
  | nil => rfl
  | cons f fs ih =>
    simpa [Nat.succ_add, advance, step, List.reverse_cons, List.append_assoc, pick]
      using ih (f.divisor::d) (pick take f :: r)

private theorem cut_last (a : Bool) (w : Word) :
    ∃ lo hi, a::w = lo++[hi] ∧ lo.length = w.length := by
  induction w generalizing a with
  | nil => exact ⟨[], a, rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨lo, hi, he, hl⟩ := ih x
    exact ⟨a::lo, hi, congrArg (a :: ·) he, by simpa using hl⟩

private theorem division_digit (x : Bool) (xs : Word) (seen d r o)
    (hw : d.length = r.length) (hr : little r < little d) :
    ∃ q : Bool, ∃ r' : Word, r'.length = d.length ∧ little r' < little d ∧
      2*little r+digit x = little d*digit q+little r' ∧
      advance (2*d.length+3) (.feed ⟨x::xs,seen⟩ d r, o) =
        (.feed ⟨xs,(x,q)::seen⟩ d r', o) := by
  obtain ⟨lo,hi,parts,wl⟩ := cut_last x r
  have len : d.length = lo.length := hw.trans wl.symm
  let fs := frames d lo false
  let take := hi || !lastBorrow d lo false
  obtain ⟨ds,os,_⟩ := frames_spec d lo false len
  have size : fs.length = d.length := by simpa [fs] using congrArg List.length ds
  have span : little (lo++[hi]) < 2 * little d := by
    rw [← parts, little]; have := digit_le x; omega
  obtain ⟨value, small⟩ := select_digit d lo hi len span
  have chosen : fs.map (pick take) = (if take then fs.map Cell.difference else lo) := by
    cases take
    · exact os
    · rfl
  refine ⟨take, fs.map (pick take), by simpa using size, ?_, ?_, ?_⟩
  · rw [chosen]; exact small
  · change little (lo++[hi]) = little d*digit take +
        little (if take then fs.map Cell.difference else lo) at value
    rw [← parts, little] at value
    rw [chosen]
    simpa only [Nat.add_comm (digit x)] using value
  · have sub := subtract_run ⟨xs,seen⟩ x hi o d lo false [] len
    have res := restore_run ⟨xs,seen⟩ x take o fs.reverse [] []
    simp only [List.append_nil] at sub
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at res
    change advance (d.length+1) (.subtract ⟨xs,seen⟩ x d (lo++[hi]) [] false, o) =
      (.restore ⟨xs,seen⟩ x take fs.reverse [] [], o) at sub
    rw [← parts] at sub
    change fs.map Cell.divisor = d at ds
    rw [ds] at res
    have joined := run_then sub res
    rw [size] at joined
    have ticks : 2*d.length+3 = ((d.length+1)+(d.length+1))+1 := by omega
    rw [ticks]
    exact joined

private theorem division_run (w : Word) (d r : Word) (seen o)
    (hw : d.length = r.length) (hr : little r < little d) :
    ∃ q r' : Word, q.length = w.length ∧ r'.length = d.length ∧ little r' < little d ∧
      2^w.length*little r + big w = little d*big q+little r' ∧
      advance (w.length*(2*d.length+3)+1) (.feed ⟨w,seen⟩ d r, o) =
        (.test ((w.zip q).reverse++seen) d r' true, o) := by
  induction w generalizing r seen with
  | nil => exact ⟨[], r, rfl, hw.symm, hr, by simp [big], by simp [advance,step]⟩
  | cons x xs ih =>
    obtain ⟨a,m,hm,rm,digitEq,one⟩ := division_digit x xs seen d r o hw hr
    obtain ⟨qs,rf,hq,hf,small,tailEq,more⟩ := ih m ((x,a)::seen) hm.symm rm
    refine ⟨a::qs,rf,by simp [hq],hf,small,?_,?_⟩
    · simp only [big, List.length_cons, Nat.pow_succ, hq]
      calc
        _ = 2^xs.length * (2*little r + digit x) + big xs := by poly
        _ = little d * (2^xs.length * digit a) + (2^xs.length * little m + big xs) := by
          rw [digitEq]; poly
        _ = _ := by rw [tailEq]; poly
    · have joined := run_then one more
      have ticks : (x::xs).length*(2*d.length+3)+1 =
          (2*d.length+3) + (xs.length*(2*d.length+3)+1) := by
        rw [List.length_cons, Nat.succ_mul]; omega
      simpa only [ticks,List.zip_cons_cons,List.reverse_cons,List.append_assoc,
        List.cons_append,List.nil_append] using joined

private theorem test_run (d o seen) (r : Word) (ok : Bool) :
    advance (r.length+1) (.test seen d r ok, o) =
      (.reload (ok && decide (little r = 0)) seen [] d, o) := by
  induction r generalizing ok with
  | nil => simp [little,advance,step]
  | cons x xs ih =>
    have even_zero : 2*little xs = 0 ↔ little xs = 0 := by omega
    have rec := ih (ok && !x)
    cases x <;> cases ok <;>
      simpa [little, digit, Nat.succ_add, advance, step, even_zero] using rec

private def choose (ok : Bool) (p : Bool × Bool) := if ok then p.2 else p.1

private def ready (ok : Bool) (w d : Word) (o : List Mark) : State :=
  if ok then (.emit w d [],.sep::o) else (.increment w d [] true,o)

private theorem reload_run (ok d o) (p : List (Bool × Bool)) (w : Word) :
    advance (p.length+1) (.reload ok p w d, o) = ready ok (p.reverse.map (choose ok)++w) d o := by
  induction p generalizing w with
  | nil => cases ok <;> rfl
  | cons a ps ih =>
    rcases a with ⟨x,y⟩
    simpa [Nat.succ_add, advance, step, List.reverse_cons, List.append_assoc,choose]
      using ih (choose ok (x,y)::w)

private theorem project_zip (ok : Bool) (w q : Word) (h : w.length = q.length) :
    (w.zip q).map (choose ok) = if ok then q else w := by
  induction w generalizing q with
  | nil => cases q <;> simp_all
  | cons x xs ih =>
    cases q with
    | nil => simp at h
    | cons y ys =>
      have tail := ih ys (by simpa using h)
      cases ok <;> simp_all [choose]

private theorem emit_run (w) (d rev : Word) (o : List Mark) :
    advance (d.length+1) (.emit w d rev, o) =
      (.replace w (d.reverse++rev) [], (d.map Mark.bit).reverse++o) := by
  induction d generalizing rev o with
  | nil => rfl
  | cons x xs ih =>
    simpa [Nat.succ_add, advance, step, List.reverse_cons, List.append_assoc]
      using ih (x::rev) (.bit x::o)

private def incBits : Word → Bool → Word
  | [], _ => []
  | x::xs, c => (x ^^ c) :: incBits xs (x && c)

private def overflow : Word → Bool → Bool
  | [], c => c
  | x::xs, c => overflow xs (x && c)

private theorem inc_spec (d : Word) (c : Bool) :
    (incBits d c).length = d.length ∧
    little (incBits d c) + 2^d.length*digit (overflow d c) = little d + digit c := by
  induction d generalizing c with
  | nil => simp [incBits,overflow,little]
  | cons x xs ih =>
    obtain ⟨len,arith⟩ := ih (x && c)
    have unit : digit (x ^^ c) + 2*digit (x && c) = digit x + digit c := by
      cases x <;> cases c <;> decide
    simp only [incBits,overflow,List.length_cons,len,true_and,little,Nat.pow_succ]
    rw [Nat.mul_right_comm (2^xs.length) 2]
    omega

private theorem increment_run (w o) (d rev : Word) (c : Bool) :
    advance (d.length+1) (.increment w d rev c, o) =
      (.replace w ((incBits d c).reverse++rev) [], o) := by
  induction d generalizing rev c with
  | nil => rfl
  | cons x xs ih =>
    simpa [Nat.succ_add,advance,step,incBits,List.reverse_cons,List.append_assoc]
      using ih ((x ^^ c)::rev) (x && c)

private theorem replace_run (w o) (rev d : Word) :
    advance (rev.length+1) (.replace w rev d, o) = (.start w (rev.reverse++d), o) := by
  induction rev generalizing d with
  | nil => rfl
  | cons x xs ih =>
    simpa [Nat.succ_add,advance,step,List.reverse_cons,List.append_assoc] using ih (x::d)


private def Within (k : Nat) (s t : State) : Prop := ∃ j ≤ k, advance j s = t

private theorem Within.exactly {k s t} (h : advance k s = t) : Within k s t := ⟨k, by omega, h⟩

private theorem Within.then {a b s t u} (h : Within a s t) (j : Within b t u) :
    Within (a+b) s u := by
  obtain ⟨i,hi,ei⟩ := h
  obtain ⟨k,hk,ek⟩ := j
  exact ⟨i+k,by omega,run_then ei ek⟩

private theorem Within.weaken {a b s t} (h : Within a s t) (le : a ≤ b) : Within b s t := by
  obtain ⟨k,hk,e⟩ := h
  exact ⟨k,Nat.le_trans hk le,e⟩

private theorem zero_value (n : Nat) : little (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,little,digit,ih]

private theorem push_zero (n : Nat) (w : Word) :
    List.replicate (n+1) false ++ w = List.replicate n false ++ false::w := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (false :: ·) ih

private theorem boot_run (xs rev zs : Word) (o : List Mark) :
    advance xs.length (.boot xs rev zs, o) =
      (.boot [] (xs.reverse++rev) (List.replicate xs.length false++zs), o) := by
  induction xs generalizing rev zs with
  | nil => rfl
  | cons x xs ih =>
    simpa [advance,step,List.reverse_cons,List.append_assoc,push_zero] using ih (x::rev) (false::zs)

private theorem home_run (rev w d : Word) (o : List Mark) :
    advance (rev.length+1) (.home rev w d, o) = (.start (rev.reverse++w) d, o) := by
  induction rev generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simpa [Nat.succ_add,advance,step,List.reverse_cons,List.append_assoc] using ih (x::w)

private def twoWord (b : Nat) : Word := false::true::List.replicate (b-2) false

private theorem boot_ready (w : Word) (h : 2 ≤ w.length) :
    advance (2*w.length+2) (.boot w [] [],[]) = (.start w (twoWord w.length),[]) := by
  have first := boot_run w [] [] []
  simp only [List.append_nil] at first
  have last := home_run w.reverse [] (twoWord w.length) []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at last
  have len : w.length = (w.length-2)+2 := by omega
  have zeros : List.replicate w.length false = false::false::List.replicate (w.length-2) false := by
    conv => lhs; rw [len]
    simp [List.replicate_succ]
  rw [zeros] at first
  have middle : advance 1 (.boot [] w.reverse (false::false::List.replicate (w.length-2) false),[]) =
        (.home w.reverse [] (twoWord w.length),[]) := rfl
  have all := run_then (run_then first middle) last
  have ticks : 2*w.length+2 = (w.length+1)+(w.length+1) := by omega
  rw [ticks]; exact all

private theorem zeros_run (w o) (d rev r : Word) :
    advance (d.length+1) (.zeros w d rev r, o) =
      (.rewind w (d.reverse++rev) [] (List.replicate d.length false++r), o) := by
  induction d generalizing rev r with
  | nil => rfl
  | cons x xs ih =>
    simpa [Nat.succ_add,advance,step,List.reverse_cons,List.append_assoc,push_zero] using ih (x::rev) (false::r)

private theorem rewind_run (w o) (rev d r : Word) :
    advance (rev.length+1) (.rewind w rev d r, o) =
      (.feed ⟨w,[]⟩ (rev.reverse++d) r,o) := by
  induction rev generalizing d with
  | nil => rfl
  | cons x xs ih =>
    simpa [Nat.succ_add,advance,step,List.reverse_cons,List.append_assoc] using ih (x::d)

private theorem start_live (w d o) (h : 2 ≤ big w) :
    ∃ v : Word, v.length ≤ w.length ∧ big v = big w ∧
      Within (w.length+1) (.start w d,o) (.zeros v d [] [],o) := by
  induction w with
  | nil => simp [big] at h
  | cons x xs ih =>
    cases x with
    | false =>
      have val : big (false::xs) = big xs := by simp [big,digit]
      obtain ⟨v,hv,eq,k,hk,run⟩ := ih (val ▸ h)
      exact ⟨v,by simp; omega,eq.trans val.symm,k+1,by simp; omega,run⟩
    | true =>
      cases xs with
      | nil => simp [big,digit] at h
      | cons a tail => exact ⟨_,Nat.le_refl _,rfl,1,by simp,rfl⟩

private theorem start_done (w d o) (h : big w ≤ 1) :
    Within (w.length+1) (.start w d,o) (.halt,o) := by
  induction w with
  | nil => exact ⟨1,by decide,rfl⟩
  | cons x xs ih =>
    cases x with
    | false =>
      obtain ⟨k,hk,run⟩ := ih (by simpa [big,digit] using h)
      exact ⟨k+1,by simp; omega,run⟩
    | true =>
      cases xs with
      | nil => exact ⟨1,by decide,rfl⟩
      | cons a tail =>
        simp only [big,List.length_cons,Nat.pow_succ,digit,Nat.mul_one] at h
        have := Nat.two_pow_pos tail.length
        omega

private theorem after_ready (ok : Bool) (w d o) :
    advance ((d.length+1)+(d.length+1)) (ready ok w d o) =
      if ok then (.start w d,packet d o) else (.start w (incBits d true),o) := by
  cases ok with
  | true =>
    have first := emit_run w d [] (.sep::o)
    have last := replace_run w (packet d o) d.reverse []
    simp only [List.append_nil] at first
    simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at last
    exact run_then first last
  | false =>
    have first := increment_run w o d [] true
    have last := replace_run w o (incBits d true).reverse []
    simp only [List.append_nil] at first
    simp only [List.length_reverse,List.reverse_reverse,List.append_nil,(inc_spec d true).1] at last
    exact run_then first last

/-- Each round costs at most this many elementary transitions on a b-bit input. -/
def roundBound (b : Nat) := 12*(b+1)^2

private theorem one_round (w d : Word) (o : List Mark) (b : Nat)
    (hw : w.length ≤ b) (hd : d.length = b) (live : 2 ≤ big w) (pos : 0 < little d) :
    ∃ v q : Word, v.length ≤ b ∧ q.length ≤ b ∧ big v = big w ∧ big q = big w/little d ∧
      Within (roundBound b) (.start w d,o)
        (if little d ∣ big w then (.start q d,packet d o) else (.start v (incBits d true),o)) := by
  obtain ⟨v,hv,val,trim⟩ := start_live w d o live
  let rz := List.replicate d.length false
  have zeros := zeros_run v o d [] []
  simp only [List.append_nil] at zeros
  have rew := rewind_run v o d.reverse [] rz
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at rew
  obtain ⟨q,r,hq,hr,small,division,scan⟩ :=
    division_run v d rz [] o (by simp [rz]) (by simpa [rz,zero_value] using pos)
  simp only [rz,zero_value,Nat.mul_zero,Nat.zero_add] at division
  simp only [List.append_nil] at scan
  have rem : big v % little d = little r := by
    rw [division,Nat.mul_add_mod,Nat.mod_eq_of_lt small]
  have quot : big v/little d = big q := by
    rw [division,Nat.add_comm,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt small,Nat.zero_add]
  let ok := decide (little r = 0)
  have take : ok = decide (little d ∣ big w) := by
    simp [ok,← val,Nat.dvd_iff_mod_eq_zero,rem]
  have test := test_run d o (v.zip q).reverse r true
  simp only [Bool.true_and] at test
  have load := reload_run ok d o (v.zip q).reverse []
  simp only [List.reverse_reverse,List.append_nil,project_zip ok v q hq.symm,
    List.length_reverse,List.length_zip,hq,Nat.min_self] at load
  have finish := after_ready ok (if ok then q else v) d o
  have run := run_then (run_then (run_then (run_then (run_then zeros rew) scan) test) load) finish
  have all := trim.then (Within.exactly run)
  have vlen := Nat.le_trans hv hw
  refine ⟨v,q,vlen,by omega,val,?_,?_⟩
  · simpa only [val] using quot.symm
  · have cost : (w.length+1) + (((((d.length+1+(d.length+1))+
          (v.length*(2*d.length+3)+1))+(r.length+1))+(v.length+1))+((d.length+1)+(d.length+1))) ≤
          roundBound b := by
      rw [hr,hd]
      have bounded := Nat.mul_le_mul_right (2*b+3) vlen
      simp only [roundBound,Nat.pow_two,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,
        Nat.mul_assoc] at bounded ⊢
      rw [Nat.mul_left_comm b 2 b] at bounded
      omega
    have bounded := all.weaken cost
    rw [take] at bounded
    by_cases hit : little d ∣ big w <;> simpa [hit] using bounded


/-- A prime is at least two and has only one and itself as divisors. -/
def Prime (p : Nat) := 2 ≤ p ∧ ∀ k, k ∣ p → k = 1 ∨ k = p

/-- Every prime divisor of n is at most B. -/
def Smooth (n B : Nat) := ∀ p, Prime p → p ∣ n → p ≤ B

def product : List Nat → Nat | [] => 1 | x::xs => x*product xs

private def PrimeOutput (o : List Mark) := ∀ p ∈ decode o 0, Prime p

private def NoEarlier (n d : Nat) := ∀ k, 2 ≤ k → k < d → ¬k ∣ n

private theorem prime_divisor (n : Nat) (h : 2 ≤ n) : ∃ p, Prime p ∧ p ∣ n := by
  classical
  by_cases prime : Prime n
  · exact ⟨n,prime,Nat.dvd_refl n⟩
  · have proper : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
      apply Classical.byContradiction
      intro none
      apply prime
      refine ⟨h,?_⟩
      intro d dvd
      by_cases one : d=1
      · exact Or.inl one
      · exact Or.inr (Classical.byContradiction (fun different => none ⟨d,dvd,one,different⟩))
    obtain ⟨d,dvd,not_one,not_self⟩ := proper
    have positive := Nat.pos_of_dvd_of_pos dvd (by omega)
    have upper := Nat.le_of_dvd (by omega : 0 < n) dvd
    obtain ⟨p,primeP,dvdP⟩ := prime_divisor d (by omega)
    exact ⟨p,primeP,Nat.dvd_trans dvdP dvd⟩
termination_by n

private theorem first_is_prime {d n : Nat} (hd : 2 ≤ d) (early : NoEarlier n d)
    (hit : d ∣ n) : Prime d := by
  refine ⟨hd,?_⟩
  intro k dvd
  have pos := Nat.pos_of_dvd_of_pos dvd (by omega)
  have upper := Nat.le_of_dvd (by omega : 0 < d) dvd
  by_cases one : k=1
  · exact Or.inl one
  · by_cases self : k=d
    · exact Or.inr self
    · exact False.elim (early k (by omega) (by omega) (Nat.dvd_trans dvd hit))

private theorem log_drop {n d q : Nat} (hd : 2 ≤ d) (hq : 0 < q) (eqn : n=d*q) :
    q.log2 + 1 ≤ n.log2 := by
  have base := (Nat.le_log2 (by omega : q ≠ 0)).mp (Nat.le_refl q.log2)
  have lower := Nat.mul_le_mul base hd
  rw [Nat.mul_comm q d, ← eqn, ← Nat.pow_succ] at lower
  have pos : 0 < n := by rw [eqn]; exact Nat.mul_pos (by omega) hq
  exact (Nat.le_log2 (by omega)).mpr lower

private theorem charge {a c : Nat} (fee extra : Nat) (less : a < c) :
    fee + (a*fee + extra) ≤ c*fee + extra := by
  have h := Nat.mul_le_mul_right fee (show a+1 ≤ c by omega)
  rw [Nat.succ_mul] at h
  omega

private theorem complete (w d : Word) (o : List Mark) (b B : Nat)
    (hw : w.length ≤ b) (hd : d.length = b) (pos : 0 < big w) (lo : 2 ≤ little d)
    (early : NoEarlier (big w) (little d)) (smooth : Smooth (big w) B) (primes : PrimeOutput o) :
    ∃ out, product (decode out 0) = big w * product (decode o 0) ∧ PrimeOutput out ∧
      Within ((B-little d+(big w).log2)*roundBound b+(b+1)) (.start w d,o) (.halt,out) := by
  by_cases terminal : big w = 1
  · refine ⟨o,by simp [terminal],primes,?_⟩
    exact (start_done w d o (by omega)).weaken (by omega)
  · have live : 2 ≤ big w := by omega
    obtain ⟨v,q,hv,hq,vEq,qEq,round⟩ := one_round w d o b hw hd live (by omega)
    by_cases hit : little d ∣ big w
    · rw [if_pos hit] at round
      have factorEq : big w = little d * big q := by
        rw [qEq]
        have E := Nat.div_add_mod (big w) (little d)
        simpa [Nat.mod_eq_zero_of_dvd hit] using E.symm
      have qpos : 0 < big q := by
        by_cases z : big q = 0
        · rw [z,Nat.mul_zero] at factorEq; omega
        · omega
      have qdvd : big q ∣ big w := ⟨little d,by simpa [Nat.mul_comm] using factorEq⟩
      have qe : NoEarlier (big q) (little d) :=
        fun k hk le dv => early k hk le (Nat.dvd_trans dv qdvd)
      have qs : Smooth (big q) B := fun p hp dv => smooth p hp (Nat.dvd_trans dv qdvd)
      have dp := first_is_prime lo early hit
      have op : PrimeOutput (packet d o) := by
        intro p member
        rw [decode_packet,List.mem_cons] at member
        rcases member with rfl | mem
        · exact dp
        · exact primes p mem
      have drop := log_drop lo qpos factorEq
      obtain ⟨out,eq,po,tail⟩ := complete q d (packet d o) b B hq hd qpos lo qe qs op
      refine ⟨out,?_,po,(round.then tail).weaken (charge _ _ (by omega))⟩
      rw [eq,decode_packet,product,factorEq]
      ac_rfl
    · rw [if_neg hit] at round
      obtain ⟨p,hp,pdvd⟩ := prime_divisor (big w) live
      have lower : little d ≤ p := by
        apply Nat.le_of_not_gt
        intro smaller
        exact early p hp.1 smaller pdvd
      have order : little d < p := by
        by_cases eq : p = little d
        · exact False.elim (hit (eq ▸ pdvd))
        · omega
      have bound := smooth p hp pdvd
      have psize := Nat.le_of_dvd pos pdvd
      have fit := Nat.lt_of_lt_of_le (big_lt w) (Nat.pow_le_pow_right (by decide : 0<2) hw)
      obtain ⟨len,inc⟩ := inc_spec d true
      have iv : little (incBits d true) = little d + 1 := by
        cases c : overflow d true <;> simp [c,digit,hd] at inc <;> omega
      have next : NoEarlier (big v) (little (incBits d true)) := by
        rw [vEq,iv]
        intro k hk lt dvd
        by_cases eq : k=little d
        · exact hit (eq ▸ dvd)
        · exact early k hk (by omega) dvd
      have rank : B-little (incBits d true)+(big v).log2 < B-little d+(big w).log2 := by
        rw [iv,vEq]; omega
      obtain ⟨out,eq,po,tail⟩ := complete v (incBits d true) o b B hv (len.trans hd)
        (vEq ▸ pos) (by omega) next (vEq ▸ smooth) primes
      exact ⟨out,vEq ▸ eq,po,(round.then tail).weaken (charge _ _ rank)⟩
termination_by B - little d + (big w).log2
decreasing_by all_goals omega

def initial (input : Word) : State := (.boot input [] [],[])

/-- A bound in elementary finite-alphabet transitions, including initialization,
binary division, divisor increments, output digits, and the final halt. -/
def timeBound (b B : Nat) := (B+b)*roundBound b + 3*(b+1)

/-- Runtime and full output correctness for the *same run*. The machine takes
only the binary input; B is a bound used in the proof. -/
theorem factor_smooth (w : Word) (B : Nat) (hn : 2 ≤ big w) (smooth : Smooth (big w) B) :
    ∃ k ≤ timeBound w.length B, ∃ out,
      advance k (initial w) = (.halt,out) ∧
      product (decode out 0) = big w ∧ ∀ p ∈ decode out 0, Prime p := by
  have width : 2 ≤ w.length := by
    have small := big_lt w
    by_cases z : w.length = 0
    · rw [z] at small; simp at small; omega
    · by_cases one : w.length = 1
      · rw [one] at small; simp at small; omega
      · omega
  let d := twoWord w.length
  have dw : d.length = w.length := by simp [d,twoWord]; omega
  have dv : little d = 2 := by simp [d,twoWord,little,digit,zero_value]
  have first : Within (2*w.length+2) (initial w) (.start w d,[]) :=
    Within.exactly (boot_ready w width)
  have early : NoEarlier (big w) (little d) := by intro k hk lt; omega
  obtain ⟨out,values,primes,last⟩ := complete w d [] w.length B (Nat.le_refl _) dw (by omega)
    (by omega) early smooth (by intro p hp; simp [decode] at hp)
  have lp := (Nat.log2_lt (by omega : big w ≠ 0)).mpr (big_lt w)
  have ticks := Nat.mul_le_mul_right (roundBound w.length)
    (show B-little d+(big w).log2 ≤ B+w.length by omega)
  obtain ⟨k,cost,run⟩ := first.then last
  exact ⟨k,by unfold timeBound; omega,out,run,by simpa [decode,product] using values,primes⟩

/-- Read the machine's output as soon as it halts. The fuel is a safe bound
for the Lean evaluator; it is not a register of the bit machine. -/
def readRun : Nat → State → List Mark
  | 0,s => s.2
  | k+1,s => match s.1 with
    | .halt => s.2
    | _ => readRun k (step s)

private theorem advance_halt (k : Nat) (o : List Mark) : advance k (.halt,o) = (.halt,o) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

private theorem readRun_eq (k : Nat) (s : State) : readRun k s = (advance k s).2 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rcases s with ⟨p,o⟩
    cases p <;> first | exact ih _ | simp [readRun,advance,step,advance_halt]

private theorem read_after_halt {k lim : Nat} {s : State} {o : List Mark}
    (h : advance k s = (.halt,o)) (le : k ≤ lim) : readRun lim s = o := by
  rw [readRun_eq,show lim=k+(lim-k) by omega,advance_add,h,advance_halt]

private def digits (n : Nat) : Nat → Word
  | 0 => []
  | k+1 => decide (n%2=1) :: digits (n/2) k

private theorem digits_len (n k : Nat) : (digits n k).length=k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [digits,ih]

private theorem digits_value (n k : Nat) (h : n < 2^k) : little (digits n k)=n := by
  induction k generalizing n with
  | zero => simp at h; simp [digits,little]; omega
  | succ k ih =>
    rw [Nat.pow_succ] at h
    change digit (decide (n%2=1))+2*little (digits (n/2) k)=n
    rw [ih (n/2) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one n with z | o <;> simp [*,digit] <;> omega

private theorem big_snoc (w : Word) (x : Bool) : big (w++[x]) = 2*big w+digit x := by
  induction w with
  | nil => simp [big]
  | cons a xs ih =>
    simp only [List.cons_append,big,ih,List.length_append,List.length_cons,
      List.length_nil,Nat.zero_add,Nat.pow_succ]
    poly

private theorem big_reverse (w : Word) : big w.reverse = little w := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [List.reverse_cons,big_snoc,ih,little,Nat.add_comm]

/-- Canonical binary input (zero is written with one digit). -/
def binary (n : Nat) : Word := (digits n (n.log2+1)).reverse

theorem binary_spec (n : Nat) : big (binary n) = n ∧ (binary n).length = n.log2+1 :=
  ⟨(big_reverse _).trans (digits_value _ _ Nat.lt_log2_self),by simp [binary,digits_len]⟩

/-- Numeric convenience interface. The binary machine itself starts at
`initial w` and runs its transition until the halt state. -/
def factor (n : Nat) : List Nat :=
  let w := binary n
  decode (readRun (timeBound w.length n) (initial w)) 0

theorem factor_correct (n : Nat) (h : 2 ≤ n) :
    product (factor n) = n ∧ ∀ p ∈ factor n, Prime p := by
  have v := (binary_spec n).1
  have sm : Smooth (big (binary n)) n := by
    intro p _ dv; rw [v] at dv; exact Nat.le_of_dvd (by omega) dv
  obtain ⟨k,hk,o,run,prod,ps⟩ := factor_smooth (binary n) n (by omega) sm
  dsimp only [factor]
  rw [read_after_halt run hk]
  exact ⟨prod.trans v,ps⟩

private theorem same_halt {a b : Nat} {s : State} {x y : List Mark}
    (h : advance a s = (.halt,x)) (j : advance b s = (.halt,y)) : x = y := by
  have one := run_then h (advance_halt b x)
  have two := run_then j (advance_halt a y)
  rw [Nat.add_comm b a] at two
  exact congrArg Prod.snd (one.symm.trans two)

private theorem decode_is_factor {n t : Nat} (h : 2 ≤ n) {o : List Mark}
    (run : advance t (initial (binary n)) = (.halt,o)) : decode o 0 = factor n := by
  have value := (binary_spec n).1
  have smooth : Smooth (big (binary n)) n := by
    intro p _ dvd; rw [value] at dvd; exact Nat.le_of_dvd (by omega) dvd
  obtain ⟨k,hk,z,ends,_,_⟩ := factor_smooth (binary n) n (by omega) smooth
  dsimp only [factor]
  rw [read_after_halt ends hk,same_halt run ends]

private theorem polynomial_budget (b e : Nat) :
    timeBound b (b^e) ≤ 27*(b+1)^(max e 1+2) := by
  let x := b+1
  let k := max e 1
  have pos : 0 < x := by dsimp [x]; omega
  have p : b^e ≤ x^k := Nat.le_trans (Nat.pow_le_pow_left (by dsimp [x]; omega) e)
    (Nat.pow_le_pow_right pos (Nat.le_max_left _ _))
  have xle : x ≤ x^k := by
    simpa using (Nat.pow_le_pow_right pos (Nat.le_max_right e 1))
  have xl : x ≤ x^(k+2) := by
    apply Nat.le_trans xle
    exact Nat.pow_le_pow_right pos (by omega)
  have b_le : b ≤ x := by dsimp [x]; omega
  have bound := Nat.mul_le_mul_right (12*x^2) (show b^e+b ≤ 2*x^k by omega)
  have rearrange : 2*x^k*(12*x^2) = 24*x^(k+2) := by
    rw [Nat.pow_add]
    calc
      _ = (2*12)*(x^k*x^2) := by ac_rfl
      _ = _ := rfl
  rw [rearrange] at bound
  change (b^e+b)*(12*x^2)+3*x ≤ 27*x^(k+2)
  omega

/-- On inputs whose prime factors are at most b^e, this one uniform binary
machine returns the same prime list as `factor` within a polynomial in b. The
algorithm is not given e, the smoothness bound, or any factors as input. -/
theorem polynomial_on_smooth (n e : Nat) (h : 2 ≤ n)
    (smooth : Smooth n ((n.log2+1)^e)) :
    let b := n.log2+1
    ∃ t ≤ 27*(b+1)^(max e 1+2), ∃ o,
      advance t (initial (binary n)) = (.halt,o) ∧ decode o 0 = factor n ∧
      product (decode o 0) = n ∧ ∀ p ∈ decode o 0, Prime p := by
  obtain ⟨v,l⟩ := binary_spec n
  obtain ⟨t,cost,o,done,prod,ps⟩ := factor_smooth (binary n) ((n.log2+1)^e)
    (by omega) (by simpa only [v] using smooth)
  rw [l] at cost
  exact ⟨t,Nat.le_trans cost (polynomial_budget _ _),o,done,decode_is_factor h done,prod.trans v,ps⟩

private def currentDivisor : State → Nat
  | (.start _ d,_) => little d
  | _ => 0

/-- For an interval containing no proper divisor, the actual machine takes
at least one transition per candidate before it reaches the far endpoint. -/
private theorem reach_candidate (w d : Word) (o : List Mark) (b D : Nat)
    (hw : w.length ≤ b) (hd : d.length = b) (live : 2 ≤ big w) (lo : 2 ≤ little d)
    (order : little d ≤ D) (fits : D ≤ big w) (early : NoEarlier (big w) D) :
    ∃ k v d', D-little d ≤ k ∧ little d'=D ∧ advance k (.start w d,o) = (.start v d',o) := by
  by_cases finish : little d=D
  · exact ⟨0,w,d,by omega,finish,rfl⟩
  · have miss := early (little d) lo (by omega)
    obtain ⟨v,q,hv,_,vEq,_,round⟩ := one_round w d o b hw hd live (by omega)
    rw [if_neg miss] at round
    obtain ⟨i,_,one⟩ := round
    have space := Nat.lt_of_lt_of_le (big_lt w) (Nat.pow_le_pow_right (by decide : 0<2) hw)
    obtain ⟨len,inc⟩ := inc_spec d true
    have next : little (incBits d true) = little d + 1 := by
      cases c : overflow d true <;> simp [c,digit,hd] at inc <;> omega
    have paid : 0 < i := by
      by_cases z : i=0
      · subst i
        have forced := congrArg currentDivisor one
        change little d = little (incBits d true) at forced
        omega
      · omega
    obtain ⟨j,src,last,hj,eq,tail⟩ := reach_candidate v (incBits d true) o b D hv
      (len.trans hd) (vEq ▸ live) (by omega) (by omega) (vEq ▸ fits) (vEq ▸ early)
    exact ⟨i+j,src,last,by omega,eq,run_then one tail⟩
termination_by D-little d
decreasing_by omega

/-- Any halting execution on a product of two primes p ≤ q has taken more
than p-2 transitions. This applies to distinct primes and to prime squares. -/
theorem prime_product_lower {p q t : Nat} (hp : Prime p) (hq : Prime q) (order : p ≤ q)
    {out : List Mark} (run : advance t (initial (binary (p*q))) = (.halt,out)) : p-2 < t := by
  let w := binary (p*q)
  let b := w.length
  let d := twoWord b
  have val : big w = p*q := (binary_spec _).1
  have pp := hp.1
  have qq := hq.1
  have fits : p ≤ p*q := by
    have h := Nat.mul_le_mul_left p (show 1≤q by omega)
    simpa using h
  have bitsBound := big_lt w
  have width : 2 ≤ b := by
    change big w < 2^b at bitsBound
    by_cases small : b < 2
    · have le := Nat.pow_le_pow_right (by decide : 0<2) (by omega : b≤1)
      simp at le; omega
    · omega
  have dw : d.length = b := by simp [d,twoWord]; omega
  have dv : little d = 2 := by simp [d,twoWord,little,digit,zero_value]
  have early : NoEarlier (big w) p := by
    rw [val]
    intro a ha lt dvd
    obtain ⟨i,j,ip,jq,decomp⟩ := Nat.dvd_mul.mp dvd
    rcases hp.2 i ip with h|h <;> rcases hq.2 j jq with g|g <;>
      simp [h,g] at decomp <;> omega
  obtain ⟨k,v,last,lower,_,path⟩ := reach_candidate w d [] b p (Nat.le_refl _) dw (by omega)
    (by omega) (by omega) (by omega) early
  have all := run_then (boot_ready w width) path
  have late : 2*w.length+2+k < t := by
    apply Nat.lt_of_not_ge
    intro le
    have after := run_then run (advance_halt (2*w.length+2+k-t) out)
    rw [show t+(2*w.length+2+k-t)=2*w.length+2+k by omega] at after
    change advance (2*w.length+2+k) (.boot w [] [],[]) = (.halt,out) at after
    rw [all] at after
    have impossible := congrArg Prod.fst after
    cases impossible
  omega

/-- Exponential lower bound in the binary length on prime squares. -/
theorem prime_square_bit_lower {p t : Nat} (hp : Prime p) {out : List Mark}
    (run : advance t (initial (binary (p*p))) = (.halt,out)) :
    2^((p*p).log2/2)-2 < t := by
  have pp := hp.1
  have pos := Nat.mul_pos (by omega : 0<p) (by omega : 0<p)
  let l := (p*p).log2
  have base : 2^l ≤ p*p := (Nat.le_log2 (by omega)).mp (Nat.le_refl _)
  have sq := Nat.pow_le_pow_right (by decide : 0<2) (by omega : l/2+l/2 ≤ l)
  rw [Nat.pow_add] at sq
  have small : 2^(l/2) ≤ p := by
    apply Nat.le_of_not_gt
    intro bigger
    have lt := Nat.mul_lt_mul_of_lt_of_le bigger (Nat.le_of_lt bigger) (Nat.two_pow_pos _)
    omega
  have cost := prime_product_lower hp hp (Nat.le_refl p) run
  change 2^(l/2)-2 < t
  omega


private def factorial : Nat → Nat | 0 => 1 | i+1 => (i+1)*factorial i

private theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

private theorem divides_factorial {d : Nat} (positive : 0<d) (k : Nat) (le : d≤k) :
    d ∣ factorial k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases eq : d=k+1
    · subst d; exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_left _ _)

private theorem prime_above (limit : Nat) : ∃ p, Prime p ∧ limit < p := by
  have pos := factorial_pos limit
  obtain ⟨p,hp,dvd⟩ := prime_divisor (factorial limit+1) (by omega)
  refine ⟨p,hp,?_⟩
  by_cases le : p ≤ limit
  · have pp := hp.1
    have fac := divides_factorial (by omega : 0<p) limit le
    have one := Nat.eq_one_of_dvd_one ((Nat.dvd_add_iff_right fac).mpr dvd)
    omega
  · omega

/- The following elementary power estimates are reused from FactorizationThreshold.lean. -/
private theorem power_log_lower {n : Nat} (hn : 0 < n) : 2 ^ n.log2 ≤ n :=
  (Nat.le_log2 (by omega)).1 (Nat.le_refl _)

private theorem square_le_exp (t : Nat) (ht : 4 ≤ t) : t*t ≤ 2^t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction u with
  | zero => decide
  | succ u ih =>
    change ((4 + u) + 1) * ((4 + u) + 1) ≤ 2 ^ ((4 + u) + 1)
    rw [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    have linear : 2*(4+u) + 1 ≤ (4+u)*(4+u) := by
      have h := Nat.mul_le_mul_right (4+u) (show 3 ≤ 4+u by omega)
      omega
    omega

/-- An explicit eventual domination bound for the binary input-length estimate below. -/
private theorem exponent_dominates (c d x : Nat) (large : 2^(c+2*d+4) ≤ x) :
    c * (2*(x+1))^d < 2^x := by
  have xp : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) large
  let t := x.log2
  have tLarge : c+2*d+4 ≤ t := (Nat.le_log2 (by omega)).2 large
  have tLower : 2^t ≤ x := power_log_lower xp
  have tUpper : x < 2^(t+1) := (Nat.log2_lt (by omega)).1 (by dsimp [t]; omega)
  have step : 2*(x+1) ≤ 2^(t+2) := by
    rw [show t+2 = (t+1)+1 by omega, Nat.pow_succ]
    omega
  have degrees := Nat.mul_le_mul_right t (show d+1 ≤ t by omega)
  rw [Nat.add_mul, Nat.one_mul] at degrees
  have sq := square_le_exp t (by omega)
  have expBound : c + (t+2)*d ≤ x := by
    rw [Nat.add_mul, Nat.mul_comm t d]
    omega
  have productBound := Nat.mul_lt_mul_of_lt_of_le
    (Nat.lt_two_pow_self (n := c)) (Nat.pow_le_pow_left step d)
    (Nat.pow_pos (Nat.two_pow_pos (t+2)))
  calc
    c * (2*(x+1))^d < 2^c * (2^(t+2))^d := productBound
    _ = 2^(c+(t+2)*d) := by
      rw [Nat.pow_add 2 c ((t+2)*d), Nat.pow_mul 2 (t+2) d]
    _ ≤ 2^x := Nat.pow_le_pow_right (by decide) expBound

private theorem square_bits_upper {p : Nat} (hp : 0 < p) :
    (p*p).log2 + 1 ≤ 2*(p.log2+1) := by
  have upper : p < 2^(p.log2+1) := (Nat.log2_lt (by omega)).1 (by omega)
  have sq := Nat.mul_lt_mul_of_lt_of_le upper (Nat.le_of_lt upper) (Nat.two_pow_pos _)
  have h : p*p < 2^(2*(p.log2+1)) := by
    rw [Nat.mul_comm 2 (p.log2+1), Nat.pow_mul, Nat.pow_two]
    exact sq
  have := (Nat.log2_lt (Nat.ne_of_gt (Nat.mul_pos hp hp))).2 h
  omega


/-- For every fixed coefficient and exponent and every minimum bit length there
is a prime square whose (terminating, correct) run exceeds that polynomial.
This lower bound applies to the sequential-divisor machine in this file. -/
theorem exceeds_every_polynomial (c e minBits : Nat) :
    ∃ p, Prime p ∧ minBits ≤ (p*p).log2+1 ∧
      (∃ t out, advance t (initial (binary (p*p))) = (.halt,out) ∧
        decode out 0 = factor (p*p)) ∧
      ∀ t out, advance t (initial (binary (p*p))) = (.halt,out) →
        c*((p*p).log2+1)^e < t := by
  let limit := 2^((c+2)+2*e+4) + minBits
  obtain ⟨p,hp,bigPrime⟩ := prime_above (2^limit)
  have pp := hp.1
  have pos : 0<p := by omega
  have psize := (Nat.le_log2 (by omega : p≠0)).mpr (Nat.le_of_lt bigPrime)
  have floor := power_log_lower pos
  have pSquare : p ≤ p*p := by simpa using Nat.mul_le_mul_left p (show 1≤p by omega)
  have logSquare : p.log2 ≤ (p*p).log2 :=
    (Nat.le_log2 (by omega)).mpr (Nat.le_trans floor pSquare)
  have hlimit : 2^((c+2)+2*e+4) ≤ p.log2 := by dsimp [limit] at psize; omega
  have minLimit : minBits ≤ limit := Nat.le_add_left _ _
  have growth := exponent_dominates (c+2) e p.log2 hlimit
  have comp := Nat.mul_le_mul_left (c+2) (Nat.pow_le_pow_left (square_bits_upper pos) e)
  have padding : 0 < ((p*p).log2+1)^e := Nat.pow_pos (by omega)
  rw [Nat.add_mul] at comp
  have v := (binary_spec (p*p)).1
  have smooth : Smooth (big (binary (p*p))) (p*p) := by
    intro q _ dvd; rw [v] at dvd; exact Nat.le_of_dvd (by omega) dvd
  obtain ⟨t,_,out,run,_,_⟩ := factor_smooth (binary (p*p)) (p*p) (by omega) smooth
  refine ⟨p,hp,by omega,⟨t,out,run,decode_is_factor (by omega) run⟩,?_⟩
  intro steps result halts
  have lower := prime_product_lower hp hp (Nat.le_refl _) halts
  omega

end BinarySmoothFactor

#print axioms BinarySmoothFactor.factor_correct
#print axioms BinarySmoothFactor.factor_smooth
#print axioms BinarySmoothFactor.polynomial_on_smooth
#print axioms BinarySmoothFactor.prime_product_lower
#print axioms BinarySmoothFactor.prime_square_bit_lower
#print axioms BinarySmoothFactor.exceeds_every_polynomial
