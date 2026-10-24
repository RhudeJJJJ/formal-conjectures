/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode094
import Proofs.RadenkovicGutmanD4Long00CompositionalNode104
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e105 : NestedArithmetic.Expr 3 := .plus e094 e104
noncomputable def p105 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-288,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2592,-2592,0],[-2592,-2496,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-68256,-29376,0],[-29376,-8480,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-673920,-142560,0],[-142560,-14656,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3631776,-392640,0],[-392640,-14208,0],[0,0]],[[0,0,0],[0,0],[0]],[[-12411488,-686432,0],[-686432,-8000],[0]],[[0,0,0],[0,0],[0]],[[-29103296,-805760,0],[-805760,-2592],[0]],[[0,0,0],[0,0],[0]],[[-49071488,-653632,0],[-653632,-448],[0]],[[0,0,0],[0,0],[0]],[[-61273056,-370560,0],[-370560,-32],[0]],[[0,0,0],[0,0],[0]],[[-57713600,-146272,0],[-146272,0],[0]],[[0,0],[0]],[[-41443008,-39360],[-39360]],[[0,0],[0]],[[-22780928,-6880],[-6880]],[[0,0],[0]],[[-9565792,-704],[-704]],[[0,0],[0]],[[-3040480,-32],[-32]],[[0,0],[0]],[[-718272,0],[0]],[[0]],[[-122112]],[[0]],[[-14112]],[[0]],[[-992]],[[0]],[[-32]],[[0]],[[0]]]
theorem step105 : p105=NestedHorner.add p094 p104 := by decide +kernel
#print axioms step105
theorem h105 : NestedArithmetic.compile e105=p105 := StagedExprCompile.compile_plus e105 e094 e104 p094 p104 p105 rfl h094 h104 step105
#print axioms h105
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
