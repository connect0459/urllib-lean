import UrllibTest.Support
import UrllibTest.Punycode
import UrllibTest.PunycodeReference
import UrllibTest.PercentEncoding
import UrllibTest.Host
import UrllibTest.Host.Ipv4
import UrllibTest.Host.Ipv6
import UrllibTest.FormUrlencoded
import UrllibTest.SearchParams
import UrllibTest.Unicode.Table
import UrllibTest.Unicode.Normalization
import UrllibTest.Unicode.Properties
import UrllibTest.Idna
import UrllibTest.Url
import UrllibTest.Url.Parser
import UrllibTest.Url.Setters

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
  total := total + (← report "unicode table" (UrllibTest.failedChecks UrllibTest.Unicode.Table.checks))
  total := total + (← report "unicode properties" (UrllibTest.failedChecks UrllibTest.Unicode.Properties.checks))
  total := total + (← report "normalization cases" UrllibTest.Unicode.Normalization.failures)
  total := total + (← report "normalization checks" (UrllibTest.failedChecks UrllibTest.Unicode.Normalization.checks))
  total := total + (← report "idna unicode (lenient)" (UrllibTest.Idna.unicodeFailures UrllibTest.Idna.lenient))
  total := total + (← report "idna ascii (lenient)" (UrllibTest.Idna.asciiFailures UrllibTest.Idna.lenient))
  total := total + (← report "idna unicode (strict)" (UrllibTest.Idna.unicodeFailures UrllibTest.Idna.strict))
  total := total + (← report "idna ascii (strict)" (UrllibTest.Idna.asciiFailures UrllibTest.Idna.strict))
  total := total + (← report "idna unicode (hyphens)" (UrllibTest.Idna.unicodeFailures UrllibTest.Idna.hyphenChecking))
  total := total + (← report "idna ascii (hyphens)" (UrllibTest.Idna.asciiFailures UrllibTest.Idna.hyphenChecking))
  total := total + (← report "idna checks" (UrllibTest.failedChecks UrllibTest.Idna.checks))
  total := total + (← report "url wpt" UrllibTest.Url.failures)
  total := total + (← report "url checks" (UrllibTest.failedChecks UrllibTest.Url.Parser.checks))
  total := total + (← report "url setters wpt" UrllibTest.Url.setterFailures)
  total := total + (← report "url toascii wpt" UrllibTest.Url.asciiFailures)
  total := total + (← report "url setter checks" (UrllibTest.failedChecks UrllibTest.Url.checks))
  return if total = 0 then 0 else 1
