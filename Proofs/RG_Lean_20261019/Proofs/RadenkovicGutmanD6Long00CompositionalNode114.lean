/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,324],[0,648],[324]],[[0,0,0],[0,0],[0]],[[0,11664,2808],[11664,5616],[2808]],[[0,0,0],[0,0],[0]],[[104976,132192,9540],[132192,19080],[9540]],[[0,0,0],[0,0],[0]],[[1469664,641520,16488],[641520,32976],[16488]],[[0,0,0],[0,0],[0]],[[9202896,1766880,15984],[1766880,31968],[15984]],[[0,0,0],[0,0],[0]],[[34299936,3088944,9000],[3088944,18000],[9000]],[[0,0,0],[0,0],[0]],[[85388256,3625920,2916],[3625920,5832],[2916]],[[0,0,0],[0,0],[0]],[[150903648,2941344,504],[2941344,1008],[504]],[[0,0,0],[0,0],[0]],[[196227504,1667520,36],[1667520,72],[36]],[[0,0],[0]],[[191848608,658224],[658224]],[[0,0],[0]],[[142750368,177120],[177120]],[[0,0],[0]],[[81233568,30960],[30960]],[[0,0],[0]],[[35291952,3168],[3168]],[[0,0],[0]],[[11601504,144],[144]],[[0]],[[2833632]],[[0]],[[497952]],[[0]],[[59472]],[[0]],[[4320]],[[0]],[[144]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
