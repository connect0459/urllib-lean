import UrllibTest.Support
import Urllib.PercentEncoding

namespace UrllibTest.PercentEncoding

open Urllib.PercentEncoding

structure EncodeCase where
  name : String
  set : EncodeSet
  input : String
  expected : String

def encodeCases : List EncodeCase := [
  { name := "c0 set encodes NUL", set := .c0Control, input := "\u0000", expected := "%00" },
  { name := "c0 set encodes the last C0 control", set := .c0Control, input := "\u001f", expected := "%1F" },
  { name := "c0 set keeps space", set := .c0Control, input := " ", expected := " " },
  { name := "c0 set keeps tilde", set := .c0Control, input := "~", expected := "~" },
  { name := "c0 set encodes DEL", set := .c0Control, input := "\u007f", expected := "%7F" },
  { name := "c0 set encodes a two-byte code point", set := .c0Control, input := "é", expected := "%C3%A9" },
  { name := "c0 set encodes a three-byte code point", set := .c0Control, input := "あ", expected := "%E3%81%82" },
  { name := "c0 set encodes a four-byte code point", set := .c0Control, input := String.singleton (Char.ofNat 0x1F600), expected := "%F0%9F%98%80" },
  { name := "fragment set encodes space", set := .fragment, input := " ", expected := "%20" },
  { name := "fragment set encodes double quote", set := .fragment, input := "\"", expected := "%22" },
  { name := "fragment set encodes less-than", set := .fragment, input := "<", expected := "%3C" },
  { name := "fragment set encodes greater-than", set := .fragment, input := ">", expected := "%3E" },
  { name := "fragment set encodes backtick", set := .fragment, input := "`", expected := "%60" },
  { name := "fragment set keeps number sign", set := .fragment, input := "#", expected := "#" },
  { name := "fragment set keeps question mark", set := .fragment, input := "?", expected := "?" },
  { name := "query set encodes space", set := .query, input := " ", expected := "%20" },
  { name := "query set encodes double quote", set := .query, input := "\"", expected := "%22" },
  { name := "query set encodes number sign", set := .query, input := "#", expected := "%23" },
  { name := "query set encodes less-than", set := .query, input := "<", expected := "%3C" },
  { name := "query set encodes greater-than", set := .query, input := ">", expected := "%3E" },
  { name := "query set keeps apostrophe", set := .query, input := "'", expected := "'" },
  { name := "query set keeps backtick", set := .query, input := "`", expected := "`" },
  { name := "special-query set encodes apostrophe", set := .specialQuery, input := "'", expected := "%27" },
  { name := "special-query set encodes number sign", set := .specialQuery, input := "#", expected := "%23" },
  { name := "special-query set keeps question mark", set := .specialQuery, input := "?", expected := "?" },
  { name := "path set encodes question mark", set := .path, input := "?", expected := "%3F" },
  { name := "path set encodes caret", set := .path, input := "^", expected := "%5E" },
  { name := "path set encodes backtick", set := .path, input := "`", expected := "%60" },
  { name := "path set encodes left brace", set := .path, input := "{", expected := "%7B" },
  { name := "path set encodes right brace", set := .path, input := "}", expected := "%7D" },
  { name := "path set encodes number sign", set := .path, input := "#", expected := "%23" },
  { name := "path set keeps slash", set := .path, input := "/", expected := "/" },
  { name := "path set keeps percent sign", set := .path, input := "%", expected := "%" },
  { name := "userinfo set encodes slash", set := .userinfo, input := "/", expected := "%2F" },
  { name := "userinfo set encodes colon", set := .userinfo, input := ":", expected := "%3A" },
  { name := "userinfo set encodes semicolon", set := .userinfo, input := ";", expected := "%3B" },
  { name := "userinfo set encodes equals sign", set := .userinfo, input := "=", expected := "%3D" },
  { name := "userinfo set encodes at sign", set := .userinfo, input := "@", expected := "%40" },
  { name := "userinfo set encodes left bracket", set := .userinfo, input := "[", expected := "%5B" },
  { name := "userinfo set encodes backslash", set := .userinfo, input := "\\", expected := "%5C" },
  { name := "userinfo set encodes right bracket", set := .userinfo, input := "]", expected := "%5D" },
  { name := "userinfo set encodes caret", set := .userinfo, input := "^", expected := "%5E" },
  { name := "userinfo set encodes vertical bar", set := .userinfo, input := "|", expected := "%7C" },
  { name := "userinfo set keeps dollar sign", set := .userinfo, input := "$", expected := "$" },
  { name := "userinfo set keeps ampersand", set := .userinfo, input := "&", expected := "&" },
  { name := "component set encodes dollar sign", set := .component, input := "$", expected := "%24" },
  { name := "component set encodes ampersand", set := .component, input := "&", expected := "%26" },
  { name := "component set encodes percent sign", set := .component, input := "%", expected := "%25" },
  { name := "userinfo set keeps percent sign", set := .userinfo, input := "%", expected := "%" },
  { name := "component set encodes plus", set := .component, input := "+", expected := "%2B" },
  { name := "component set encodes comma", set := .component, input := ",", expected := "%2C" },
  { name := "component set keeps left parenthesis", set := .component, input := "(", expected := "(" },
  { name := "component set keeps exclamation mark", set := .component, input := "!", expected := "!" },
  { name := "component set keeps hyphen, dot, underscore and tilde", set := .component, input := "-._~", expected := "-._~" },
  { name := "component set encodes only members of a mixed string", set := .component, input := "a b&c", expected := "a%20b%26c" },
  { name := "empty string stays empty", set := .component, input := "", expected := "" },
  { name := "fragment set encodes a C0 control", set := .fragment, input := String.singleton (Char.ofNat 1), expected := "%01" },
  { name := "fragment set encodes a non-ASCII code point", set := .fragment, input := "é", expected := "%C3%A9" },
  { name := "query set encodes a C0 control", set := .query, input := String.singleton (Char.ofNat 1), expected := "%01" },
  { name := "query set encodes a non-ASCII code point", set := .query, input := "é", expected := "%C3%A9" },
  { name := "special-query set encodes a C0 control", set := .specialQuery, input := String.singleton (Char.ofNat 1), expected := "%01" },
  { name := "special-query set encodes a non-ASCII code point", set := .specialQuery, input := "é", expected := "%C3%A9" },
  { name := "path set encodes a C0 control", set := .path, input := String.singleton (Char.ofNat 1), expected := "%01" },
  { name := "path set encodes a non-ASCII code point", set := .path, input := "é", expected := "%C3%A9" },
  { name := "userinfo set encodes a C0 control", set := .userinfo, input := String.singleton (Char.ofNat 1), expected := "%01" },
  { name := "userinfo set encodes a non-ASCII code point", set := .userinfo, input := "é", expected := "%C3%A9" },
  { name := "component set encodes a C0 control", set := .component, input := String.singleton (Char.ofNat 1), expected := "%01" },
  { name := "component set encodes a non-ASCII code point", set := .component, input := "é", expected := "%C3%A9" }
]

def encodeFailures : List String :=
  encodeCases.filterMap fun c =>
    if utf8PercentEncode c.set c.input == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval encodeFailures

structure DecodeCase where
  name : String
  input : String
  expected : String

def decodeText (input : String) : String :=
  utf8DecodeWithoutBom (percentDecodeString input)

def decodeCases : List DecodeCase := [
  { name := "decodes an uppercase hex escape", input := "%41", expected := "A" },
  { name := "decodes a lowercase hex escape", input := "%7a", expected := "z" },
  { name := "decodes consecutive escapes", input := "%41%42", expected := "AB" },
  { name := "keeps an escape with non-hex digits", input := "%zz", expected := "%zz" },
  { name := "keeps an escape with one hex digit", input := "%4", expected := "%4" },
  { name := "keeps a lone percent sign", input := "%", expected := "%" },
  { name := "keeps a percent sign before a valid escape", input := "%%41", expected := "%A" },
  { name := "keeps an escape whose second digit is not hex", input := "%4z", expected := "%4z" },
  { name := "decodes a multi-byte sequence", input := "%e3%81%82", expected := "あ" },
  { name := "keeps unescaped text", input := "abc", expected := "abc" },
  { name := "keeps empty input", input := "", expected := "" },
  { name := "replaces an incomplete sequence", input := "%C3", expected := String.singleton (Char.ofNat 0xFFFD) },
  { name := "replaces an invalid lead byte", input := "%FF", expected := String.singleton (Char.ofNat 0xFFFD) },
  { name := "strips one leading byte order mark", input := "%EF%BB%BFabc", expected := "abc" },
  { name := "strips only the first byte order mark", input := "%EF%BB%BF%EF%BB%BFabc", expected := String.singleton (Char.ofNat 0xFEFF) ++ "abc" }
]

def decodeFailures : List String :=
  decodeCases.filterMap fun c => if decodeText c.input == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval decodeFailures

structure Utf8Case where
  name : String
  bytes : List UInt8
  expected : List Nat

def utf8Cases : List Utf8Case := [
  { name := "decodes ASCII", bytes := [0x41], expected := [0x41] },
  { name := "decodes the smallest two-byte sequence", bytes := [0xC2, 0x80], expected := [0x80] },
  { name := "decodes the smallest three-byte sequence", bytes := [0xE0, 0xA0, 0x80], expected := [0x800] },
  { name := "decodes a four-byte sequence", bytes := [0xF0, 0x9F, 0x98, 0x80], expected := [0x1F600] },
  { name := "replaces a truncated two-byte sequence once", bytes := [0xE3, 0x81], expected := [0xFFFD] },
  { name := "replaces an overlong lead byte and its continuation separately", bytes := [0xC0, 0x80], expected := [0xFFFD, 0xFFFD] },
  { name := "replaces a surrogate encoding byte by byte", bytes := [0xED, 0xA0, 0x80], expected := [0xFFFD, 0xFFFD, 0xFFFD] },
  { name := "replaces an overlong three-byte encoding byte by byte", bytes := [0xE0, 0x80, 0x80], expected := [0xFFFD, 0xFFFD, 0xFFFD] },
  { name := "replaces an overlong four-byte encoding byte by byte", bytes := [0xF0, 0x80, 0x80, 0x80], expected := [0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD] },
  { name := "replaces a code point above U+10FFFF byte by byte", bytes := [0xF4, 0x90, 0x80, 0x80], expected := [0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD] },
  { name := "keeps the byte that interrupts a sequence", bytes := [0xE3, 0x81, 0x41], expected := [0xFFFD, 0x41] },
  { name := "replaces a truncated four-byte sequence at the end of input", bytes := [0xF0, 0x9F, 0x98], expected := [0xFFFD] },
  { name := "replaces a lone continuation byte", bytes := [0x80], expected := [0xFFFD] },
  { name := "replaces a lone two-byte lead", bytes := [0xC3], expected := [0xFFFD] },
  { name := "decodes empty input", bytes := [], expected := [] },
  { name := "replaces a lone three-byte lead", bytes := [0xEF], expected := [0xFFFD] },
  { name := "keeps the byte after a lone three-byte lead", bytes := [0xEF, 0x41], expected := [0xFFFD, 0x41] },
  { name := "replaces a three-byte lead with one continuation at the end of input", bytes := [0xEF, 0xBB], expected := [0xFFFD] },
  { name := "keeps the byte after a three-byte lead with one continuation", bytes := [0xEF, 0xBB, 0x41], expected := [0xFFFD, 0x41] },
  { name := "strips a byte order mark and keeps the following text", bytes := [0xEF, 0xBB, 0xBF, 0x41], expected := [0x41] }
]

def utf8Failures : List String :=
  utf8Cases.filterMap fun c =>
    let decoded := (utf8DecodeWithoutBom (ByteArray.mk c.bytes.toArray)).toList.map Char.toNat
    if decoded == c.expected then none else some c.name

/-- info: [] -/
#guard_msgs in
#eval utf8Failures

def guardChecks : List UrllibTest.Check := [
  { name := "keeps a lone percent sign as a byte", holds := (percentDecode (ByteArray.mk #[0x25])).toList == [0x25] },
  { name := "decodes an escape of two decimal digits", holds := (percentDecode (ByteArray.mk #[0x25, 0x34, 0x31])).toList == [0x41] },
  { name := "keeps an incomplete escape", holds := (percentDecode (ByteArray.mk #[0x25, 0x34])).toList == [0x25, 0x34] },
  { name := "decodes an escape of uppercase hexadecimal digits", holds := (percentDecode (ByteArray.mk #[0x25, 0x46, 0x46])).toList == [0xFF] },
  { name := "escapes the zero byte", holds := percentEncodeByte 0x00 == "%00" },
  { name := "escapes the largest byte", holds := percentEncodeByte 0xFF == "%FF" },
  { name := "escapes a letter byte with uppercase digits", holds := percentEncodeByte 0x7A == "%7A" },
  { name := "keeps a code point outside the set", holds := utf8PercentEncodeCodePoint .path 'a' == "a" },
  { name := "escapes a code point inside the set", holds := utf8PercentEncodeCodePoint .path ' ' == "%20" },
  { name := "escapes every byte of a multi-byte code point", holds := utf8PercentEncodeCodePoint .path 'é' == "%C3%A9" },
  { name := "percent-encodes a byte outside the set as itself", holds := percentEncodeBytes .path (ByteArray.mk #[0x61]) == "a" },
  { name := "percent-encodes a byte inside the set", holds := percentEncodeBytes .path (ByteArray.mk #[0x20]) == "%20" },
  { name := "percent-encodes a non-ASCII byte in every set", holds := EncodeSet.all.all fun set => percentEncodeBytes set (ByteArray.mk #[0x80]) == "%80" },
  { name := "percent-encodes bytes that are not valid UTF-8", holds := percentEncodeBytes .c0Control (ByteArray.mk #[0x41, 0xFF, 0xC0]) == "A%FF%C0" },
  { name := "percent-encodes the empty byte sequence to the empty string", holds := percentEncodeBytes .path ByteArray.empty == "" },
  { name := "percent-encodes the UTF-8 bytes of a string like the string encoder", holds := ["", "a b", "é<あ>", "x\u0000y", String.singleton (Char.ofNat 0x1F600)].all fun s => EncodeSet.all.all fun set => percentEncodeBytes set s.toUTF8 == utf8PercentEncode set s },
  { name := "strictly decodes valid UTF-8", holds := utf8DecodeWithoutBomOrFail (ByteArray.mk #[0xE3, 0x81, 0x82]) == some "あ" },
  { name := "strictly decodes the empty byte sequence", holds := utf8DecodeWithoutBomOrFail ByteArray.empty == some "" },
  { name := "strict decoding strips one leading byte order mark", holds := utf8DecodeWithoutBomOrFail (ByteArray.mk #[0xEF, 0xBB, 0xBF, 0x41]) == some "A" },
  { name := "strict decoding keeps an encoded U+FFFD", holds := utf8DecodeWithoutBomOrFail (ByteArray.mk #[0xEF, 0xBF, 0xBD]) == some (String.singleton (Char.ofNat 0xFFFD)) },
  { name := "strict decoding fails on a truncated sequence", holds := utf8DecodeWithoutBomOrFail (ByteArray.mk #[0xE3, 0x81]) == none },
  { name := "strict decoding fails on an overlong encoding", holds := utf8DecodeWithoutBomOrFail (ByteArray.mk #[0xC0, 0x80]) == none },
  { name := "strict decoding fails on a surrogate encoding", holds := utf8DecodeWithoutBomOrFail (ByteArray.mk #[0xED, 0xA0, 0x80]) == none },
  { name := "strict decoding fails on a code point above U+10FFFF", holds := utf8DecodeWithoutBomOrFail (ByteArray.mk #[0xF4, 0x90, 0x80, 0x80]) == none },
  { name := "strict decoding fails on a lone continuation byte", holds := utf8DecodeWithoutBomOrFail (ByteArray.mk #[0x80]) == none },
  { name := "strict decoding agrees with replacement decoding on every valid case", holds := utf8Cases.all fun c => match utf8DecodeWithoutBomOrFail (ByteArray.mk c.bytes.toArray) with | some text => text == utf8DecodeWithoutBom (ByteArray.mk c.bytes.toArray) | none => c.expected.contains 0xFFFD }
]

/-- info: [] -/
#guard_msgs in
#eval UrllibTest.failedChecks guardChecks

end UrllibTest.PercentEncoding
