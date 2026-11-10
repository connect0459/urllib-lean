import Urllib.UrlPattern.Canonicalize
import Urllib.Regex.Parser

namespace Urllib.UrlPattern

/-- A compiled component of a URL pattern. -/
structure Component where
  /-- The normalized pattern string. -/
  patternString : String
  /-- The regular expression. -/
  regexp : Regex.Regex
  /-- The group names, in order. -/
  groupNames : List String
  /-- Whether a part has a custom regular expression. -/
  hasRegexpGroups : Bool
  /-- The parts of the pattern string. -/
  parts : List Part
  /-- The options the component was compiled with. -/
  options : Options
  /-- The encoding callback of the component, which `generate` applies to a group value. -/
  encode : String → Except Error String

/-- Compiles a component: parses the pattern string, generates the regular expression, and compiles it. -/
def compileComponent (input : String) (encode : String → Except Error String) (options : Options) :
    Except Error Component := do
  let parts ← parsePattern input options encode
  let (regexpString, names) := generateRegexp parts options
  match Regex.Regex.compile regexpString options.ignoreCase with
  | .error _ => throw .regexp
  | .ok regexp =>
    return { patternString := generatePattern parts options, regexp := regexp, groupNames := names,
             hasRegexpGroups := parts.any fun p => p.type == .regexp, parts := parts,
             options := options, encode := encode }

/-- Whether the component's regular expression matches one of the special schemes. -/
def Component.matchesSpecialScheme (c : Component) : Bool :=
  Url.specialSchemes.any fun scheme => c.regexp.test scheme

end Urllib.UrlPattern
