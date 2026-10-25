/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode035
import Proofs.RadenkovicGutmanD36Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3888],[0,-3888]],[[0,0,0],[0,0,0],[0,0]],[[0,-34992,-34992],[-34992,-139968,-16848],[-34992,-16848]],[[0,0,0],[0,0,0],[0,0]],[[-629856,-1399680,-244944],[-1399680,-979776,-20736],[-244944,-20736]],[[0,0,0],[0,0,0],[0,0]],[[-15536448,-11664000,-676512],[-11664000,-2706048,-9072],[-676512,-9072]],[[0,0,0],[0,0,0],[0,0]],[[-138848256,-46155744,-981072],[-46155744,-3924288,-1296],[-981072,-1296]],[[0,0,0],[0,0],[0]],[[-674319168,-107860896,-824256],[-107860896,-3297024],[-824256]],[[0,0,0],[0,0],[0]],[[-2085468768,-163980288,-413424],[-163980288,-1653696],[-413424]],[[0,0,0],[0,0],[0]],[[-4456871424,-170462880,-121824],[-170462880,-487296],[-121824]],[[0,0,0],[0,0],[0]],[[-6903086976,-124256592,-19440],[-124256592,-77760],[-19440]],[[0,0,0],[0,0],[0]],[[-7979749344,-64070352,-1296],[-64070352,-5184],[-1296]],[[0,0],[0]],[[-7009330464,-23235984],[-23235984]],[[0,0],[0]],[[-4725234144,-5793120],[-5793120]],[[0,0],[0]],[[-2453068800,-944784],[-944784]],[[0,0],[0]],[[-977951232,-90720],[-90720]],[[0,0],[0]],[[-296485920,-3888],[-3888]],[[0]],[[-67075776]],[[0]],[[-10958976]],[[0]],[[-1220832]],[[0]],[[-82944]],[[0]],[[-2592]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
