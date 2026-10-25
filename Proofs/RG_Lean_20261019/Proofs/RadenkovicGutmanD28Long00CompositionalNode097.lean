/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode051
import Proofs.RadenkovicGutmanD28Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2352],[0,-2352]],[[0,0,0],[0,0,0],[0,0]],[[0,21168,-35280],[21168,-105840,-10360],[-35280,-10360]],[[0,0,0],[0,0,0],[0,0]],[[317520,-700056,-271992],[-700056,-781704,-13272],[-271992,-13272]],[[0,0,0],[0,0,0],[0,0]],[[-1821960,-8537256,-835352],[-8537256,-2298240,-6384],[-835352,-6384]],[[0,0,0],[0,0,0],[0,0]],[[-53725896,-40148864,-1340864],[-40148864,-3553256,-1176],[-1340864,-1176]],[[0,0,0],[0,0,0],[0,0]],[[-374048976,-105777000,-1237208],[-105777000,-3182704,-56],[-1237208,-56]],[[0,0,0],[0,0],[0]],[[-1418035864,-177203824,-677712],[-177203824,-1705984],[-677712]],[[0,0,0],[0,0],[0]],[[-3493188552,-200385304,-218568],[-200385304,-542752],[-218568]],[[0,0,0],[0,0],[0]],[[-6043266544,-157581984,-38976],[-157581984,-96488],[-38976]],[[0,0,0],[0,0],[0]],[[-7658122640,-87192056,-3192],[-87192056,-8064],[-3192]],[[0,0,0],[0,0],[0]],[[-7284337480,-33846904,-56],[-33846904,-168],[-56]],[[0,0],[0]],[[-5272550304,-9044336],[-9044336]],[[0,0],[0]],[[-2921270912,-1594208],[-1594208]],[[0,0],[0]],[[-1237834640,-169904],[-169904]],[[0,0],[0]],[[-397971112,-8960],[-8960]],[[0,0],[0]],[[-95478600,-112],[-112]],[[0]],[[-16600080]],[[0]],[[-1988560]],[[0]],[[-149576]],[[0]],[[-5768]],[[0]],[[-56]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
