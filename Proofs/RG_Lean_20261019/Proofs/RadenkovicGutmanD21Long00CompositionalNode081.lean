/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode079
import Proofs.RadenkovicGutmanD21Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-23814,0],[-23814,-3969,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-392931,-345303,0],[-345303,-34398,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6417873,-2127384,0],[-2127384,-116865,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-46627812,-7371315,0],[-7371315,-201978,0],[0,0]],[[0,0,0],[0,0],[0]],[[-200322045,-16066512,0],[-16066512,-195804],[0]],[[0,0,0],[0,0],[0]],[[-571151889,-23380497,0],[-23380497,-110250],[0]],[[0,0,0],[0,0],[0]],[[-1150028334,-23512356,0],[-23512356,-35721],[0]],[[0,0,0],[0,0],[0]],[[-1698342156,-16646868,0],[-16646868,-6174],[0]],[[0,0,0],[0,0],[0]],[[-1884366099,-8348130,0],[-8348130,-441],[0]],[[0,0],[0]],[[-1594715094,-2945439],[-2945439]],[[0,0],[0]],[[-1038012570,-714420],[-714420]],[[0,0],[0]],[[-520983288,-113337],[-113337]],[[0,0],[0]],[[-200966787,-10584],[-10584]],[[0,0],[0]],[[-58986837,-441],[-441]],[[0]],[[-12925710]],[[0]],[[-2046240]],[[0]],[[-220941]],[[0]],[[-14553]],[[0]],[[-441]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
