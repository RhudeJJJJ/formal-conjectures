/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode092
import Proofs.RadenkovicGutmanD6Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-432,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3888,-3888,0],[-3888,-3636,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-101412,-43092,0],[-43092,-11784,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-985284,-202824,0],[-202824,-18804,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5194944,-535500,0],[-535500,-15816,0],[0,0]],[[0,0,0],[0,0],[0]],[[-17255316,-882408,0],[-882408,-6672],[0]],[[0,0,0],[0,0],[0]],[[-39000636,-951228,0],[-951228,-888],[0]],[[0,0,0],[0,0],[0]],[[-62693496,-678288,0],[-678288,300],[0]],[[0,0,0],[0,0],[0]],[[-73507776,-310728,0],[-310728,120],[0]],[[0,0,0],[0,0],[0]],[[-63593004,-80448,0],[-80448,12],[0]],[[0,0],[0]],[[-40521912,-4188],[-4188]],[[0,0],[0]],[[-18630264,4440],[4440]],[[0,0],[0]],[[-5805840,1524],[1524]],[[0,0],[0]],[[-973548,216],[216]],[[0,0],[0]],[[62772,12],[12]],[[0]],[[86184]],[[0]],[[24624]],[[0]],[[3804]],[[0]],[[324]],[[0]],[[12]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
