/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode033
import Proofs.RadenkovicGutmanD40Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4800],[0,4800]],[[0,0,0],[0,0,0],[0,0]],[[0,-43200,43200],[-43200,158400,20800],[43200,20800]],[[0,0,0],[0,0,0],[0,0]],[[-648000,475200,302400],[475200,1084800,25600],[302400,25600]],[[0,0,0],[0,0,0],[0,0]],[[-4104000,6681600,835200],[6681600,2916800,11200],[835200,11200]],[[0,0,0],[0,0,0],[0,0]],[[2246400,30238400,1211200],[30238400,4112000,1600],[1211200,1600]],[[0,0,0],[0,0],[0]],[[105700800,74870400,1017600],[74870400,3360000],[1017600]],[[0,0,0],[0,0],[0]],[[502446400,117617600,510400],[117617600,1641600],[510400]],[[0,0,0],[0,0],[0]],[[1329872000,125142400,150400],[125142400,472000],[150400]],[[0,0,0],[0,0],[0]],[[2360544000,93006400,24000],[93006400,73600],[24000]],[[0,0,0],[0,0],[0]],[[3014840000,48811200,1600],[48811200,4800],[1600]],[[0,0],[0]],[[2867680000,18000000],[18000000]],[[0,0],[0]],[[2067590400,4560000],[4560000]],[[0,0],[0]],[[1138291200,755200],[755200]],[[0,0],[0]],[[478216000,73600],[73600]],[[0,0],[0]],[[152020800,3200],[3200]],[[0]],[[35913600]],[[0]],[[6105600]],[[0]],[[705600]],[[0]],[[49600]],[[0]],[[1600]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
