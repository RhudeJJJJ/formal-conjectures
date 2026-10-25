/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode079
import Proofs.RadenkovicGutmanD41Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-90774,0],[-90774,-15129,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1497771,-1316223,0],[-1316223,-131118,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-24463593,-8109144,0],[-8109144,-445465,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-177735492,-28097915,0],[-28097915,-769898,0],[0,0]],[[0,0,0],[0,0],[0]],[[-763585845,-61242192,0],[-61242192,-746364],[0]],[[0,0,0],[0,0],[0]],[[-2177111849,-89121577,0],[-89121577,-420250],[0]],[[0,0,0],[0,0],[0]],[[-4383668094,-89624196,0],[-89624196,-136161],[0]],[[0,0,0],[0,0],[0]],[[-6473725996,-63454388,0],[-63454388,-23534],[0]],[[0,0,0],[0,0],[0]],[[-7182810459,-31821330,0],[-31821330,-1681],[0]],[[0,0],[0]],[[-6078721254,-11227399],[-11227399]],[[0,0],[0]],[[-3956687370,-2723220],[-2723220]],[[0,0],[0]],[[-1985879608,-432017],[-432017]],[[0,0],[0]],[[-766043467,-40344],[-40344]],[[0,0],[0]],[[-224845517,-1681],[-1681]],[[0]],[[-49270110]],[[0]],[[-7799840]],[[0]],[[-842181]],[[0]],[[-55473]],[[0]],[[-1681]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
