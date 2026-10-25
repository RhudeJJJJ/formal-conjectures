/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1600]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-28800,28800],[0,28800]],[[0,0,0],[0,0,0],[0,0]],[[129600,-259200,129600],[-259200,268800,76800],[129600,76800]],[[0,0,0],[0,0,0],[0,0]],[[-86400,-604800,691200],[-604800,1916800,70400],[691200,70400]],[[0,0,0],[0,0,0],[0,0]],[[-4795200,4406400,1555200],[4406400,4755200,25600],[1555200,25600]],[[0,0,0],[0,0,0],[0,0]],[[-13200000,27609600,1920000],[27609600,6259200,3200],[1920000,3200]],[[0,0,0],[0,0],[0]],[[27784000,73052800,1417600],[73052800,4870400],[1417600]],[[0,0,0],[0,0],[0]],[[263622400,116848000,640000],[116848000,2300800],[640000]],[[0,0,0],[0,0],[0]],[[823638400,124947200,172800],[124947200,646400],[172800]],[[0,0,0],[0,0],[0]],[[1583702400,92979200,25600],[92979200,99200],[25600]],[[0,0,0],[0,0],[0]],[[2131494400,48809600,1600],[48809600,6400],[1600]],[[0,0],[0]],[[2113651200,18000000],[18000000]],[[0,0],[0]],[[1581555200,4560000],[4560000]],[[0,0],[0]],[[901840000,755200],[755200]],[[0,0],[0]],[[392059200,73600],[73600]],[[0,0],[0]],[[128902400,3200],[3200]],[[0]],[[31484800]],[[0]],[[5532800]],[[0]],[[660800]],[[0]],[[48000]],[[0]],[[1600]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
