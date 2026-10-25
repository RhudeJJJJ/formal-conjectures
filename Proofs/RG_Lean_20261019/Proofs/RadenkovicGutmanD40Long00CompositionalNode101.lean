/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode051
import Proofs.RadenkovicGutmanD40Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1600]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,38400],[0,38400,80]],[[0,0,0],[0,0,0],[0,0]],[[-129600,86400,216000],[86400,865440,119840],[216000,119840]],[[0,0,0],[0,0,0],[0,0]],[[-684720,5801760,1302480],[5801760,5222400,125440],[1302480,125440]],[[0,0,0],[0,0,0],[0,0]],[[31721760,47725920,3260160],[47725920,13083040,51520],[3260160,51520]],[[0,0,0],[0,0,0],[0,0]],[[378501360,182484320,4420160],[182484320,17753920,7680],[4420160,7680]],[[0,0,0],[0,0,0],[0,0]],[[1995853280,413326080,3548800],[413326080,14266240,160],[3548800,160]],[[0,0,0],[0,0],[0]],[[6375243280,612830560,1731680],[612830560,6966720],[1731680]],[[0,0,0],[0,0],[0]],[[13830872000,625106400,505600],[625106400,2035360],[505600]],[[0,0,0],[0,0],[0]],[[21598801760,449625280,82240],[449625280,331200],[82240]],[[0,0,0],[0,0],[0]],[[25105070240,229989760,6080],[229989760,24480],[6080]],[[0,0,0],[0,0],[0]],[[22153704960,83212000,80],[83212000,320],[80]],[[0,0],[0]],[[15003993600,20845600],[20845600]],[[0,0],[0]],[[7830348800,3455200],[3455200]],[[0,0],[0]],[[3141846560,345600],[345600]],[[0,0],[0]],[[960462480,16800],[16800]],[[0,0],[0]],[[219766080,160],[160]],[[0]],[[36504800]],[[0]],[[4176800]],[[0]],[[298640]],[[0]],[[10720]],[[0]],[[80]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
