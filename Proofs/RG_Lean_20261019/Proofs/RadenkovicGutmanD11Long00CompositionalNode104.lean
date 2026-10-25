/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode092
import Proofs.RadenkovicGutmanD11Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-792,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7128,-7128,0],[-7128,-6666,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-185922,-79002,0],[-79002,-21604,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1806354,-371844,0],[-371844,-34474,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9524064,-981750,0],[-981750,-28996,0],[0,0]],[[0,0,0],[0,0],[0]],[[-31634746,-1617748,0],[-1617748,-12232],[0]],[[0,0,0],[0,0],[0]],[[-71501166,-1743918,0],[-1743918,-1628],[0]],[[0,0,0],[0,0],[0]],[[-114938076,-1243528,0],[-1243528,550],[0]],[[0,0,0],[0,0],[0]],[[-134764256,-569668,0],[-569668,220],[0]],[[0,0,0],[0,0],[0]],[[-116587174,-147488,0],[-147488,22],[0]],[[0,0],[0]],[[-74290172,-7678],[-7678]],[[0,0],[0]],[[-34155484,8140],[8140]],[[0,0],[0]],[[-10644040,2794],[2794]],[[0,0],[0]],[[-1784838,396],[396]],[[0,0],[0]],[[115082,22],[22]],[[0]],[[158004]],[[0]],[[45144]],[[0]],[[6974]],[[0]],[[594]],[[0]],[[22]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
