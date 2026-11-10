import UrllibTest.Support
import UrllibTest.Punycode
import UrllibTest.PunycodeReference
import UrllibTest.PercentEncoding
import UrllibTest.Host
import UrllibTest.Host.Ipv4
import UrllibTest.Host.Ipv6
import UrllibTest.FormUrlencoded
import UrllibTest.SearchParams

def report (name : String) (failures : List String) : IO Nat := do
  IO.println s!"{name}: {failures.length} failures"
  for failure in failures do
    IO.println s!"  - {failure}"
  return failures.length

def main : IO UInt32 := do
  let mut total := 0
  total := total + (← report "punycode samples encode" UrllibTest.Punycode.rfc3492SamplesEncodedExactly)
  total := total + (← report "punycode samples decode" UrllibTest.Punycode.rfc3492SamplesDecodedExactly)
  total := total + (← report "punycode checks" (UrllibTest.failedChecks UrllibTest.Punycode.guardChecks))
  total := total + (← report "punycode reference samples" UrllibTest.PunycodeReference.rfc3492Disagreements)
  total := total + (← report "punycode reference generated" (UrllibTest.PunycodeReference.generatedDisagreements.map toString))
  total := total + (← report "punycode reference checks" (UrllibTest.failedChecks UrllibTest.PunycodeReference.guardChecks))
  total := total + (← report "percent encode" UrllibTest.PercentEncoding.encodeFailures)
  total := total + (← report "percent decode" UrllibTest.PercentEncoding.decodeFailures)
  total := total + (← report "utf8 decode" UrllibTest.PercentEncoding.utf8Failures)
  total := total + (← report "percent checks" (UrllibTest.failedChecks UrllibTest.PercentEncoding.guardChecks))
  total := total + (← report "ipv4 parse" UrllibTest.Host.Ipv4.parseFailures)
  total := total + (← report "ipv4 ends in number" UrllibTest.Host.Ipv4.endsInNumberFailures)
  total := total + (← report "ipv4 checks" (UrllibTest.failedChecks UrllibTest.Host.Ipv4.guardChecks))
  total := total + (← report "ipv6 parse" UrllibTest.Host.Ipv6.parseFailures)
  total := total + (← report "ipv6 checks" (UrllibTest.failedChecks UrllibTest.Host.Ipv6.guardChecks))
  total := total + (← report "host domain" (UrllibTest.Host.parseFailures UrllibTest.Host.domainCases))
  total := total + (← report "host ipv4" (UrllibTest.Host.parseFailures UrllibTest.Host.ipv4Cases))
  total := total + (← report "host ipv6" (UrllibTest.Host.parseFailures UrllibTest.Host.ipv6Cases))
  total := total + (← report "host opaque" (UrllibTest.Host.parseFailures UrllibTest.Host.opaqueCases))
  total := total + (← report "host checks" (UrllibTest.failedChecks UrllibTest.Host.guardChecks))
  total := total + (← report "form-urlencoded parse" UrllibTest.FormUrlencoded.parseFailures)
  total := total + (← report "form-urlencoded serialize" UrllibTest.FormUrlencoded.serializeFailures)
  total := total + (← report "form-urlencoded checks" (UrllibTest.failedChecks UrllibTest.FormUrlencoded.guardChecks))
  total := total + (← report "search params" (UrllibTest.failedChecks UrllibTest.SearchParams.checks))
  return if total = 0 then 0 else 1
