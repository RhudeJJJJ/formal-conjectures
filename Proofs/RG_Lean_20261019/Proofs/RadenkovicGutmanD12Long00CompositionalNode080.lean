/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode035
import Proofs.RadenkovicGutmanD12Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-432],[0,-432]],[[0,0,0],[0,0,0],[0,0]],[[0,-3888,-3888],[-3888,-15552,-1872],[-3888,-1872]],[[0,0,0],[0,0,0],[0,0]],[[-69984,-155520,-27216],[-155520,-108864,-2304],[-27216,-2304]],[[0,0,0],[0,0,0],[0,0]],[[-1726272,-1296000,-75168],[-1296000,-300672,-1008],[-75168,-1008]],[[0,0,0],[0,0,0],[0,0]],[[-15427584,-5128416,-109008],[-5128416,-436032,-144],[-109008,-144]],[[0,0,0],[0,0],[0]],[[-74924352,-11984544,-91584],[-11984544,-366336],[-91584]],[[0,0,0],[0,0],[0]],[[-231718752,-18220032,-45936],[-18220032,-183744],[-45936]],[[0,0,0],[0,0],[0]],[[-495207936,-18940320,-13536],[-18940320,-54144],[-13536]],[[0,0,0],[0,0],[0]],[[-767009664,-13806288,-2160],[-13806288,-8640],[-2160]],[[0,0,0],[0,0],[0]],[[-886638816,-7118928,-144],[-7118928,-576],[-144]],[[0,0],[0]],[[-778814496,-2581776],[-2581776]],[[0,0],[0]],[[-525026016,-643680],[-643680]],[[0,0],[0]],[[-272563200,-104976],[-104976]],[[0,0],[0]],[[-108661248,-10080],[-10080]],[[0,0],[0]],[[-32942880,-432],[-432]],[[0]],[[-7452864]],[[0]],[[-1217664]],[[0]],[[-135648]],[[0]],[[-9216]],[[0]],[[-288]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
