import JT913

/-- info: 'JT913.mainTheorem_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JT913.mainTheorem_verified
/-- info: 'JT913.conventionalTheorem_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JT913.conventionalTheorem_verified

example (r : ℕ) (hr : 1 ≤ r) :
    (JT913.K (2 * 2 ^ r) (2 ^ r) (2 ^ r - 1)).chromaticNumber =
      ((Nat.choose (2 * 2 ^ r) (2 ^ r) / (2 ^ r + 1) : ℕ) : ℕ∞) :=
  JT913.conventionalTheorem_verified r hr
