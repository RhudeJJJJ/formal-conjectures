/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode035
import Proofs.RadenkovicGutmanD16Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-2304],[0,-4608],[-2304]],[[0,0,0],[0,0],[0]],[[0,-76032,-19968],[-76032,-39936],[-19968]],[[0,0,0],[0,0],[0]],[[-622080,-850176,-67840],[-850176,-135680],[-67840]],[[0,0,0],[0,0],[0]],[[-8501760,-4061952,-117248],[-4061952,-234496],[-117248]],[[0,0,0],[0,0],[0]],[[-51826176,-10995200,-113664],[-10995200,-227328],[-113664]],[[0,0,0],[0,0],[0]],[[-187600896,-18873088,-64000],[-18873088,-128000],[-64000]],[[0,0,0],[0,0],[0]],[[-452760576,-21743872,-20736],[-21743872,-41472],[-20736]],[[0,0,0],[0,0],[0]],[[-774685696,-17314816,-3584],[-17314816,-7168],[-3584]],[[0,0,0],[0,0],[0]],[[-974439936,-9640704,-256],[-9640704,-512],[-256]],[[0,0],[0]],[[-921077248,-3739904],[-3739904]],[[0,0],[0]],[[-662458368,-989696],[-989696]],[[0,0],[0]],[[-364384768,-170240],[-170240]],[[0,0],[0]],[[-153041408,-17152],[-17152]],[[0,0],[0]],[[-48647168,-768],[-768]],[[0]],[[-11492352]],[[0]],[[-1953792]],[[0]],[[-225792]],[[0]],[[-15872]],[[0]],[[-512]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
