/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode092
import Proofs.RadenkovicGutmanD40Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2880,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25920,-25920,0],[-25920,-24240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-676080,-287280,0],[-287280,-78560,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6568560,-1352160,0],[-1352160,-125360,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34632960,-3570000,0],[-3570000,-105440,0],[0,0]],[[0,0,0],[0,0],[0]],[[-115035440,-5882720,0],[-5882720,-44480],[0]],[[0,0,0],[0,0],[0]],[[-260004240,-6341520,0],[-6341520,-5920],[0]],[[0,0,0],[0,0],[0]],[[-417956640,-4521920,0],[-4521920,2000],[0]],[[0,0,0],[0,0],[0]],[[-490051840,-2071520,0],[-2071520,800],[0]],[[0,0,0],[0,0],[0]],[[-423953360,-536320,0],[-536320,80],[0]],[[0,0],[0]],[[-270146080,-27920],[-27920]],[[0,0],[0]],[[-124201760,29600],[29600]],[[0,0],[0]],[[-38705600,10160],[10160]],[[0,0],[0]],[[-6490320,1440],[1440]],[[0,0],[0]],[[418480,80],[80]],[[0]],[[574560]],[[0]],[[164160]],[[0]],[[25360]],[[0]],[[2160]],[[0]],[[80]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
