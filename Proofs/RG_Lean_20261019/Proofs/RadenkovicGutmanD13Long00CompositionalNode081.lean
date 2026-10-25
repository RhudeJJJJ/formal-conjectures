/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode079
import Proofs.RadenkovicGutmanD13Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-9126,0],[-9126,-1521,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-150579,-132327,0],[-132327,-13182,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2459457,-815256,0],[-815256,-44785,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17868708,-2824835,0],[-2824835,-77402,0],[0,0]],[[0,0,0],[0,0],[0]],[[-76767405,-6157008,0],[-6157008,-75036],[0]],[[0,0,0],[0,0],[0]],[[-218876801,-8959873,0],[-8959873,-42250],[0]],[[0,0,0],[0,0],[0]],[[-440713806,-9010404,0],[-9010404,-13689],[0]],[[0,0,0],[0,0],[0]],[[-650838604,-6379412,0],[-6379412,-2366],[0]],[[0,0,0],[0,0],[0]],[[-722126691,-3199170,0],[-3199170,-169],[0]],[[0,0],[0]],[[-611126646,-1128751],[-1128751]],[[0,0],[0]],[[-397787130,-273780],[-273780]],[[0,0],[0]],[[-199651192,-43433],[-43433]],[[0,0],[0]],[[-77014483,-4056],[-4056]],[[0,0],[0]],[[-22604933,-169],[-169]],[[0]],[[-4953390]],[[0]],[[-784160]],[[0]],[[-84669]],[[0]],[[-5577]],[[0]],[[-169]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
