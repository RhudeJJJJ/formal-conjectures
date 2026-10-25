/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode092
import Proofs.RadenkovicGutmanD32Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2304,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20736,-20736,0],[-20736,-19392,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-540864,-229824,0],[-229824,-62848,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5254848,-1081728,0],[-1081728,-100288,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27706368,-2856000,0],[-2856000,-84352,0],[0,0]],[[0,0,0],[0,0],[0]],[[-92028352,-4706176,0],[-4706176,-35584],[0]],[[0,0,0],[0,0],[0]],[[-208003392,-5073216,0],[-5073216,-4736],[0]],[[0,0,0],[0,0],[0]],[[-334365312,-3617536,0],[-3617536,1600],[0]],[[0,0,0],[0,0],[0]],[[-392041472,-1657216,0],[-1657216,640],[0]],[[0,0,0],[0,0],[0]],[[-339162688,-429056,0],[-429056,64],[0]],[[0,0],[0]],[[-216116864,-22336],[-22336]],[[0,0],[0]],[[-99361408,23680],[23680]],[[0,0],[0]],[[-30964480,8128],[8128]],[[0,0],[0]],[[-5192256,1152],[1152]],[[0,0],[0]],[[334784,64],[64]],[[0]],[[459648]],[[0]],[[131328]],[[0]],[[20288]],[[0]],[[1728]],[[0]],[[64]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
