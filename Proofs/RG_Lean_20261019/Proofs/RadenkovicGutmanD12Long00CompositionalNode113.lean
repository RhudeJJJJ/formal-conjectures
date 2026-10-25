/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,144]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2592,2592],[0,2592]],[[0,0,0],[0,0,0],[0,0]],[[11664,-23328,11664],[-23328,24192,6912],[11664,6912]],[[0,0,0],[0,0,0],[0,0]],[[-7776,-54432,62208],[-54432,172512,6336],[62208,6336]],[[0,0,0],[0,0,0],[0,0]],[[-431568,396576,139968],[396576,427968,2304],[139968,2304]],[[0,0,0],[0,0,0],[0,0]],[[-1188000,2484864,172800],[2484864,563328,288],[172800,288]],[[0,0,0],[0,0],[0]],[[2500560,6574752,127584],[6574752,438336],[127584]],[[0,0,0],[0,0],[0]],[[23726016,10516320,57600],[10516320,207072],[57600]],[[0,0,0],[0,0],[0]],[[74127456,11245248,15552],[11245248,58176],[15552]],[[0,0,0],[0,0],[0]],[[142533216,8368128,2304],[8368128,8928],[2304]],[[0,0,0],[0,0],[0]],[[191834496,4392864,144],[4392864,576],[144]],[[0,0],[0]],[[190228608,1620000],[1620000]],[[0,0],[0]],[[142339968,410400],[410400]],[[0,0],[0]],[[81165600,67968],[67968]],[[0,0],[0]],[[35285328,6624],[6624]],[[0,0],[0]],[[11601216,288],[288]],[[0]],[[2833632]],[[0]],[[497952]],[[0]],[[59472]],[[0]],[[4320]],[[0]],[[144]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
