/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode289
import Proofs.RadenkovicGutmanD6Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[144,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[4320,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[59472,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[497952,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2833632,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[11601504,144,0],[144,0],[0]],[[0,0,0],[0,0],[0]],[[35291952,3168,0],[3168,0],[0]],[[0,0,0],[0,0],[0]],[[81233568,30960,0],[30960,0],[0]],[[0,0,0],[0,0],[0]],[[142750368,177120,0],[177120,0],[0]],[[0,0,0],[0,0],[0]],[[191848608,658224,0],[658224,0],[0]],[[0,0,0],[0,0],[0]],[[196227504,1667520,36],[1667520,72],[36]],[[0,0,0],[0,0],[0]],[[150903648,2941344,504],[2941344,1008],[504]],[[0,0,0],[0,0],[0]],[[85388256,3625920,2916],[3625920,5832],[2916]],[[0,0,0],[0,0],[0]],[[34299936,3088944,9000],[3088944,18000],[9000]],[[0,0,0],[0,0],[0]],[[9202896,1766880,15984],[1766880,31968],[15984]],[[0,0,0],[0,0],[0]],[[1469664,641520,16488],[641520,32976],[16488]],[[0,0,0],[0,0],[0]],[[104976,132192,9540],[132192,19080],[9540]],[[0,0,0],[0,0],[0]],[[0,11664,2808],[11664,5616],[2808]],[[0,0,0],[0,0],[0]],[[0,0,324],[0,648],[324]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
