/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,81]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1458,1458],[0,1458]],[[0,0,0],[0,0,0],[0,0]],[[6561,-13122,6561],[-13122,13608,3888],[6561,3888]],[[0,0,0],[0,0,0],[0,0]],[[-4374,-30618,34992],[-30618,97038,3564],[34992,3564]],[[0,0,0],[0,0,0],[0,0]],[[-242757,223074,78732],[223074,240732,1296],[78732,1296]],[[0,0,0],[0,0,0],[0,0]],[[-668250,1397736,97200],[1397736,316872,162],[97200,162]],[[0,0,0],[0,0],[0]],[[1406565,3698298,71766],[3698298,246564],[71766]],[[0,0,0],[0,0],[0]],[[13345884,5915430,32400],[5915430,116478],[32400]],[[0,0,0],[0,0],[0]],[[41696694,6325452,8748],[6325452,32724],[8748]],[[0,0,0],[0,0],[0]],[[80174934,4707072,1296],[4707072,5022],[1296]],[[0,0,0],[0,0],[0]],[[107906904,2470986,81],[2470986,324],[81]],[[0,0],[0]],[[107003592,911250],[911250]],[[0,0],[0]],[[80066232,230850],[230850]],[[0,0],[0]],[[45655650,38232],[38232]],[[0,0],[0]],[[19847997,3726],[3726]],[[0,0],[0]],[[6525684,162],[162]],[[0]],[[1593918]],[[0]],[[280098]],[[0]],[[33453]],[[0]],[[2430]],[[0]],[[81]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
