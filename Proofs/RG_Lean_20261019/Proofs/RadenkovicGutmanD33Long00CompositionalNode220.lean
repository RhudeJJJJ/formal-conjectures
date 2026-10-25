/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode217
import Proofs.RadenkovicGutmanD33Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-2178],[0],[0]],[[0,0],[0,0],[0]],[[-67518,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-960498,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-8311248,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-48887388,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-206940492,-3267,0],[-3267,0],[0]],[[0,0,0],[0,0],[0]],[[-651023802,-72963,0],[-72963,0],[0]],[[0,0,0],[0,0],[0]],[[-1550058642,-724185,0],[-724185,0],[0]],[[0,0,0],[0,0],[0]],[[-2818035792,-4210074,0],[-4210074,0],[0]],[[0,0,0],[0,0],[0]],[[-3918176262,-15909201,0],[-15909201,0],[0]],[[0,0,0],[0,0],[0]],[[-4145176134,-41010651,-1089],[-41010651,-2178],[-1089]],[[0,0,0],[0,0],[0]],[[-3295440324,-73655604,-15246],[-73655604,-30492],[-15246]],[[0,0,0],[0,0],[0]],[[-1926001044,-92496393,-88209],[-92496393,-176418],[-88209]],[[0,0,0],[0,0],[0]],[[-798036624,-80284347,-272250],[-80284347,-544500],[-272250]],[[0,0,0],[0,0],[0]],[[-220463694,-46772550,-483516],[-46772550,-967032],[-483516]],[[0,0,0],[0,0],[0]],[[-36165690,-17279163,-498762],[-17279163,-997524],[-498762]],[[0,0,0],[0,0],[0]],[[-2646270,-3616569,-288585],[-3616569,-577170],[-288585]],[[0,0,0],[0,0],[0]],[[0,-323433,-84942],[-323433,-169884],[-84942]],[[0,0,0],[0,0],[0]],[[0,0,-9801],[0,-19602],[-9801]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
