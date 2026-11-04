namespace UrllibTest

structure Check where
  name : String
  holds : Bool

def failedChecks (checks : List Check) : List String :=
  checks.filterMap fun check => if check.holds then none else some check.name

end UrllibTest
