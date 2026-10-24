/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerDataElaboration
namespace Gebendorfer.RadenkovicGutman.NoncomputableIntegerDataMacroProbe
set_option maxHeartbeats 0
noncomputable def input : NestedInteger.Poly 3 := [[[1,2],[3]],[[4],[5]]]
def output : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.add input input)
theorem checked : output=NestedInteger.add input input := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.NoncomputableIntegerDataMacroProbe
