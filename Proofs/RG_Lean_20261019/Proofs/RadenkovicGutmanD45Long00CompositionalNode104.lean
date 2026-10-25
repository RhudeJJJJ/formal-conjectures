/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode092
import Proofs.RadenkovicGutmanD45Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29160,-29160,0],[-29160,-27270,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-760590,-323190,0],[-323190,-88380,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7389630,-1521180,0],[-1521180,-141030,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-38962080,-4016250,0],[-4016250,-118620,0],[0,0]],[[0,0,0],[0,0],[0]],[[-129414870,-6618060,0],[-6618060,-50040],[0]],[[0,0,0],[0,0],[0]],[[-292504770,-7134210,0],[-7134210,-6660],[0]],[[0,0,0],[0,0],[0]],[[-470201220,-5087160,0],[-5087160,2250],[0]],[[0,0,0],[0,0],[0]],[[-551308320,-2330460,0],[-2330460,900],[0]],[[0,0,0],[0,0],[0]],[[-476947530,-603360,0],[-603360,90],[0]],[[0,0],[0]],[[-303914340,-31410],[-31410]],[[0,0],[0]],[[-139726980,33300],[33300]],[[0,0],[0]],[[-43543800,11430],[11430]],[[0,0],[0]],[[-7301610,1620],[1620]],[[0,0],[0]],[[470790,90],[90]],[[0]],[[646380]],[[0]],[[184680]],[[0]],[[28530]],[[0]],[[2430]],[[0]],[[90]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
