/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode079
import Proofs.RadenkovicGutmanD18Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-17496,0],[-17496,-2916,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-288684,-253692,0],[-253692,-25272,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4715172,-1562976,0],[-1562976,-85860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34257168,-5415660,0],[-5415660,-148392,0],[0,0]],[[0,0,0],[0,0],[0]],[[-147175380,-11803968,0],[-11803968,-143856],[0]],[[0,0,0],[0,0],[0]],[[-419621796,-17177508,0],[-17177508,-81000],[0]],[[0,0,0],[0,0],[0]],[[-844918776,-17274384,0],[-17274384,-26244],[0]],[[0,0,0],[0,0],[0]],[[-1247761584,-12230352,0],[-12230352,-4536],[0]],[[0,0,0],[0,0],[0]],[[-1384432236,-6133320,0],[-6133320,-324],[0]],[[0,0],[0]],[[-1171627416,-2163996],[-2163996]],[[0,0],[0]],[[-762621480,-524880],[-524880]],[[0,0],[0]],[[-382763232,-83268],[-83268]],[[0,0],[0]],[[-147649068,-7776],[-7776]],[[0,0],[0]],[[-43337268,-324],[-324]],[[0]],[[-9496440]],[[0]],[[-1503360]],[[0]],[[-162324]],[[0]],[[-10692]],[[0]],[[-324]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
