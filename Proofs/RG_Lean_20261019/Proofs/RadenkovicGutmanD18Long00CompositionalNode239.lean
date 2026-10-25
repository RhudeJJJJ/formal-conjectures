/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode236
import Proofs.RadenkovicGutmanD18Long00CompositionalNode238
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e239 : NestedArithmetic.Expr 3 := .plus e236 e238
noncomputable def p239 : NestedHorner.Poly 3 := [[[-324],[0],[0]],[[0,0],[0,0],[0]],[[-10692,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-162324,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1503360,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9496440,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-43337268,-324,0],[-324,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-147649068,-7776,0],[-7776,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-382763232,-83268,0],[-83268,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-762621480,-524880,0],[-524880,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1171627416,-2163996,0],[-2163996,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1384432236,-6133320,0],[-6133320,-324,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1247761584,-12230352,0],[-12230352,-4536,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-844918776,-17274384,0],[-17274384,-26244,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-419621796,-17177508,0],[-17177508,-81000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-147175380,-11803968,0],[-11803968,-143856,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34257168,-5415660,0],[-5415660,-148392,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4715172,-1562976,0],[-1562976,-85860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-288684,-253692,0],[-253692,-25272,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-17496,0],[-17496,-2916,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step239 : p239=NestedHorner.add p236 p238 := by decide +kernel
#print axioms step239
theorem h239 : NestedArithmetic.compile e239=p239 := StagedExprCompile.compile_plus e239 e236 e238 p236 p238 p239 rfl h236 h238 step239
#print axioms h239
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
