/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode035
import Proofs.RadenkovicGutmanD16Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-768],[0,-768]],[[0,0,0],[0,0,0],[0,0]],[[0,-6912,-11520],[-6912,-36864,-3424],[-11520,-3424]],[[0,0,0],[0,0,0],[0,0]],[[-124416,-429408,-89184],[-429408,-276864,-4512],[-89184,-4512]],[[0,0,0],[0,0,0],[0,0]],[[-4328640,-4038912,-275360],[-4038912,-830080,-2304],[-275360,-2304]],[[0,0,0],[0,0,0],[0,0]],[[-44813952,-17529088,-444992],[-17529088,-1310976,-480],[-444992,-480]],[[0,0,0],[0,0,0],[0,0]],[[-240279552,-44435904,-414368],[-44435904,-1202816,-32],[-414368,-32]],[[0,0,0],[0,0],[0]],[[-803796096,-72800576,-230016],[-72800576,-664064],[-230016]],[[0,0,0],[0,0],[0]],[[-1837383872,-81208320,-75744],[-81208320,-220032],[-75744]],[[0,0,0],[0,0],[0]],[[-3022990336,-63383104,-14016],[-63383104,-41728],[-14016]],[[0,0,0],[0,0],[0]],[[-3695573248,-35005344,-1248],[-35005344,-3968],[-1248]],[[0,0,0],[0,0],[0]],[[-3423744448,-13651616,-32],[-13651616,-128],[-32]],[[0,0],[0]],[[-2431366208,-3697440],[-3697440]],[[0,0],[0]],[[-1329998784,-670144],[-670144]],[[0,0],[0]],[[-559827968,-75552],[-75552]],[[0,0],[0]],[[-180006400,-4544],[-4544]],[[0,0],[0]],[[-43554880,-96],[-96]],[[0]],[[-7728512]],[[0]],[[-963328]],[[0]],[[-78272]],[[0]],[[-3584]],[[0]],[[-64]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
