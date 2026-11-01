import Mathlib

namespace Calendar

/-! ### Gregorian calendar utilities -/

/-- Returns true if `year` is a leap year according to Gregorian calendar rules.
A year is a leap year if it is divisible by 4, except for century years,
which must be divisible by 400. -/
def isLeapYear (year : Nat) : Bool :=
  ((year % 4 = 0 ∧ year % 100 ≠ 0) ∨ (year % 400 = 0))

/-- Returns true if `month` has 31 days (January, March, May, July, August, October, December). -/
def isThirtyOneDayMonth (month : Nat) : Bool :=
  month = 1 ∨ month = 3 ∨ month = 5 ∨ month = 7 ∨ month = 8 ∨ month = 10 ∨ month = 12

/-- Returns the number of days in `month` of `year` according to Gregorian calendar rules.
Returns `0` if `month` is not in the range 1..12. -/
def daysInMonth (year : Nat) (month : Nat) : Nat :=
  if month = 2 then
    if isLeapYear year then 29 else 28
  else if isThirtyOneDayMonth month then
    31
  else if 1 ≤ month ∧ month ≤ 12 then
    30
  else
    0

/-- Returns the number of days in `year` (366 for leap years, 365 otherwise). -/
def daysInYear (year : Nat) : Nat :=
  if isLeapYear year then 366 else 365

/-! ### Time unit conversions -/

/-- Convert hours and minutes to total minutes. -/
def hoursMinutesToMinutes (h m : Nat) : Nat := h * 60 + m

/-- Extract the hours component from a total number of seconds.
This is the hours field from `decomposeSeconds`. -/
def hoursFromSeconds (totalSeconds : Nat) : Nat := totalSeconds / 3600

/-- Extract the minutes component (0-59) from a total number of seconds.
This is the minutes field from `decomposeSeconds`. -/
def minutesFromSeconds (totalSeconds : Nat) : Nat := (totalSeconds % 3600) / 60

/-- Decompose a total number of seconds into (days, hours, minutes, remaining seconds).
Days use 86400 seconds, hours use 3600 seconds, minutes use 60 seconds.
This is the inverse of `hoursMinutesToMinutes` composed with `* 3600` and `* 86400`. -/
def decomposeSeconds (total_seconds : Nat) : Nat × Nat × Nat × Nat :=
  (total_seconds / 86400, (total_seconds % 86400) / 3600, (total_seconds % 3600) / 60, total_seconds % 60)

/-! ### Cumulative day counts -/

/-- Days elapsed before a given month (1-indexed) in a given year.
Returns 0 for months ≤ 1 or outside 1..12. -/
def daysBeforeMonth (year month : Nat) : Nat :=
  match month with
  | 1 => 0
  | 2 => 31
  | 3 => 31 + (if isLeapYear year then 29 else 28)
  | 4 => 31 + (if isLeapYear year then 29 else 28) + 31
  | 5 => 31 + (if isLeapYear year then 29 else 28) + 31 + 30
  | 6 => 31 + (if isLeapYear year then 29 else 28) + 31 + 30 + 31
  | 7 => 31 + (if isLeapYear year then 29 else 28) + 31 + 30 + 31 + 30
  | 8 => 31 + (if isLeapYear year then 29 else 28) + 31 + 30 + 31 + 30 + 31
  | 9 => 31 + (if isLeapYear year then 29 else 28) + 31 + 30 + 31 + 30 + 31 + 31
  | 10 => 31 + (if isLeapYear year then 29 else 28) + 31 + 30 + 31 + 30 + 31 + 31 + 30
  | 11 => 31 + (if isLeapYear year then 29 else 28) + 31 + 30 + 31 + 30 + 31 + 31 + 30 + 31
  | 12 => 31 + (if isLeapYear year then 29 else 28) + 31 + 30 + 31 + 30 + 31 + 31 + 30 + 31 + 30
  | _ => 0

/-! ### Epoch / timestamp utilities -/

/-- Total days elapsed in all years strictly before `year`, measured from a given `epoch` year.
Assumes `epoch ≤ year`; uses truncated subtraction. -/
def daysBeforeYearFrom (epoch year : Nat) : Nat :=
  let rec aux (k acc : Nat) : Nat :=
    if k = 0 then acc else aux (k - 1) (acc + daysInYear (epoch + (k - 1)))
  aux (year - epoch) 0

/-- Number of days since the `epoch` year (starting at Jan 1) for a given date.
`day` is 1-indexed. -/
def daysSinceEpoch (epoch year month day : Nat) : Nat :=
  daysBeforeYearFrom epoch year + daysBeforeMonth year month + (day - 1)

/-- Number of seconds since the `epoch` year (starting at Jan 1 00:00:00) for a given datetime.
All fields are 1-indexed where applicable (`month`, `day`). -/
def epochSecondsFrom (epoch year month day hour minute second : Nat) : Nat :=
  let days := daysSinceEpoch epoch year month day
  days * 86400 + hour * 3600 + minute * 60 + second

/-! ### `Int`-valued year variants

The definitions below are `Int`-based versions of the main `Nat`-based calendar functions.
They are needed when working with dates that involve negative years (e.g., astronomical
year numbering or dates before year 1), such as Unix timestamp conversions where
integer arithmetic on potentially negative offsets is required. -/

/-- Returns true if `year` is a leap year according to Gregorian calendar rules.
This `Int` version handles negative years via `Int` modular arithmetic. -/
def isLeapYearInt (y : Int) : Bool :=
  (y % 4 = 0) && ((y % 100 ≠ 0) || (y % 400 = 0))

/-- Returns the number of days in `month` of `year` according to Gregorian calendar rules.
Returns `0` if `month` is not in the range 1..12. This `Int` version delegates to
`isLeapYearInt` for February. -/
def daysInMonthInt (y : Int) (m : Nat) : Nat :=
  match m with
  | 1 => 31
  | 2 => if isLeapYearInt y then 29 else 28
  | 3 => 31
  | 4 => 30
  | 5 => 31
  | 6 => 30
  | 7 => 31
  | 8 => 31
  | 9 => 30
  | 10 => 31
  | 11 => 30
  | 12 => 31
  | _ => 0

end Calendar

