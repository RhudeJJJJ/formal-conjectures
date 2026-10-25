/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode235
import Proofs.RadenkovicGutmanD10Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e236 : NestedArithmetic.Expr 3 := .times e235 e122
noncomputable def p236 : NestedHorner.Poly 3 := [[[100],[0],[0]],[[0,0],[0,0],[0]],[[3100,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[44100,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[381600,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2244600,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[9501300,200,0],[200,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[29888500,4600,0],[4600,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[71143200,47200,0],[47200,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[129224400,285000,0],[285000,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[179230000,1125000,0],[1125000,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[188427500,3050700,100],[3050700,300,0],[100,0]],[[0,0,0],[0,0,0],[0,0]],[[147534000,5812900,1500],[5812900,4600,0],[1500,0]],[[0,0,0],[0,0,0],[0,0]],[[83117000,7821400,9400],[7821400,29500,0],[9400,0]],[[0,0,0],[0,0,0],[0,0]],[[31402900,7351100,31900],[7351100,102600,0],[31900,0]],[[0,0,0],[0,0,0],[0,0]],[[6606300,4679400,63600],[4679400,210000,0],[63600,0]],[[0,0,0],[0,0,0],[0,0]],[[140400,1889900,75700],[1889900,257000,100],[75700,100]],[[0,0,0],[0,0,0],[0,0]],[[-256500,417600,52200],[417600,182300,700],[52200,700]],[[0,0,0],[0,0,0],[0,0]],[[-40500,29700,18900],[29700,67800,1600],[18900,1600]],[[0,0,0],[0,0,0],[0,0]],[[0,-2700,2700],[-2700,9900,1300],[2700,1300]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,300],[0,300]]]
theorem step236 : p236=NestedArithmetic.mul p235 p122 := by decide +kernel
#print axioms step236
theorem h236 : NestedArithmetic.compile e236=p236 := StagedExprCompile.compile_times e236 e235 e122 p235 p122 p236 rfl h235 h122 step236
#print axioms h236
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
