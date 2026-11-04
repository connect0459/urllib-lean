import Urllib.PercentEncoding

namespace Urllib.PercentEncoding

theorem decodeBytes_percentEncodeByte :
    ∀ n, n < 256 →
      decodeBytes (percentEncodeByte (UInt8.ofNat n)).toUTF8.toList = [UInt8.ofNat n] := by
  decide +kernel

theorem component_contains_percent : EncodeSet.component.contains '%' = true := by
  decide

theorem userinfo_lacks_percent : EncodeSet.userinfo.contains '%' = false := by
  decide

end Urllib.PercentEncoding
