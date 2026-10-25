/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode217
import Proofs.RadenkovicGutmanD6Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-72],[0],[0]],[[0,0],[0,0],[0]],[[-2232,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-31752,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-274752,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-1616112,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-6841008,-108,0],[-108,0],[0]],[[0,0,0],[0,0],[0]],[[-21521448,-2412,0],[-2412,0],[0]],[[0,0,0],[0,0],[0]],[[-51241608,-23940,0],[-23940,0],[0]],[[0,0,0],[0,0],[0]],[[-93158208,-139176,0],[-139176,0],[0]],[[0,0,0],[0,0],[0]],[[-129526488,-525924,0],[-525924,0],[0]],[[0,0,0],[0,0],[0]],[[-137030616,-1355724,-36],[-1355724,-72],[-36]],[[0,0,0],[0,0],[0]],[[-108940176,-2434896,-504],[-2434896,-1008],[-504]],[[0,0,0],[0,0],[0]],[[-63669456,-3057732,-2916],[-3057732,-5832],[-2916]],[[0,0,0],[0,0],[0]],[[-26381376,-2654028,-9000],[-2654028,-18000],[-9000]],[[0,0,0],[0,0],[0]],[[-7288056,-1546200,-15984],[-1546200,-31968],[-15984]],[[0,0,0],[0,0],[0]],[[-1195560,-571212,-16488],[-571212,-32976],[-16488]],[[0,0,0],[0,0],[0]],[[-87480,-119556,-9540],[-119556,-19080],[-9540]],[[0,0,0],[0,0],[0]],[[0,-10692,-2808],[-10692,-5616],[-2808]],[[0,0,0],[0,0],[0]],[[0,0,-324],[0,-648],[-324]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
