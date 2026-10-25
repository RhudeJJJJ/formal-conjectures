/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode035
import Proofs.RadenkovicGutmanD20Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-3600],[0,-7200,2160],[-3600,2160]],[[0,0,0],[0,0,0],[0,0]],[[0,-99360,-11760],[-99360,15360,9360],[-11760,9360]],[[0,0,0],[0,0,0],[0,0]],[[-622080,-550800,30080],[-550800,332320,11520],[30080,11520]],[[0,0,0],[0,0,0],[0,0]],[[-4652640,133200,192640],[133200,1136960,5040],[192640,5040]],[[0,0,0],[0,0,0],[0,0]],[[-3840480,8462080,367440],[8462080,1824960,720],[367440,720]],[[0,0,0],[0,0],[0]],[[81495360,30433520,357920],[30433520,1631680],[357920]],[[0,0,0],[0,0],[0]],[[451155360,57125360,197280],[57125360,853920],[197280]],[[0,0,0],[0,0],[0]],[[1265593280,67647200,62080],[67647200,259520],[62080]],[[0,0,0],[0,0],[0]],[[2312485920,53967840,10400],[53967840,42400],[10400]],[[0,0,0],[0,0],[0]],[[2994010880,29751040,720],[29751040,2880],[720]],[[0,0],[0]],[[2858981280,11362480],[11362480]],[[0,0],[0]],[[2055778880,2952400],[2952400]],[[0,0],[0]],[[1123688800,498080],[498080]],[[0,0],[0]],[[467295040,49200],[49200]],[[0,0],[0]],[[146757600,2160],[2160]],[[0]],[[34211520]],[[0]],[[5735520]],[[0]],[[653440]],[[0]],[[45280]],[[0]],[[1440]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
