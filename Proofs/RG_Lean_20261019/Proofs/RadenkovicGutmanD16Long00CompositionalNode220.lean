/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode217
import Proofs.RadenkovicGutmanD16Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-512],[0],[0]],[[0,0],[0,0],[0]],[[-15872,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-225792,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-1953792,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-11492352,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-48647168,-768,0],[-768,0],[0]],[[0,0,0],[0,0],[0]],[[-153041408,-17152,0],[-17152,0],[0]],[[0,0,0],[0,0],[0]],[[-364384768,-170240,0],[-170240,0],[0]],[[0,0,0],[0,0],[0]],[[-662458368,-989696,0],[-989696,0],[0]],[[0,0,0],[0,0],[0]],[[-921077248,-3739904,0],[-3739904,0],[0]],[[0,0,0],[0,0],[0]],[[-974439936,-9640704,-256],[-9640704,-512],[-256]],[[0,0,0],[0,0],[0]],[[-774685696,-17314816,-3584],[-17314816,-7168],[-3584]],[[0,0,0],[0,0],[0]],[[-452760576,-21743872,-20736],[-21743872,-41472],[-20736]],[[0,0,0],[0,0],[0]],[[-187600896,-18873088,-64000],[-18873088,-128000],[-64000]],[[0,0,0],[0,0],[0]],[[-51826176,-10995200,-113664],[-10995200,-227328],[-113664]],[[0,0,0],[0,0],[0]],[[-8501760,-4061952,-117248],[-4061952,-234496],[-117248]],[[0,0,0],[0,0],[0]],[[-622080,-850176,-67840],[-850176,-135680],[-67840]],[[0,0,0],[0,0],[0]],[[0,-76032,-19968],[-76032,-39936],[-19968]],[[0,0,0],[0,0],[0]],[[0,0,-2304],[0,-4608],[-2304]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
