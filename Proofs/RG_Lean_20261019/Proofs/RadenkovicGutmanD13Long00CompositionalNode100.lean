/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode043
import Proofs.RadenkovicGutmanD13Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-1521],[0,-3042,858],[-1521,858]],[[0,0,0],[0,0,0],[0,0]],[[0,-60723,-5460],[-60723,1950,3718],[-5460,3718]],[[0,0,0],[0,0,0],[0,0]],[[-568620,-512811,9269],[-512811,104338,4576],[9269,4576]],[[0,0,0],[0,0,0],[0,0]],[[-6991920,-1690299,71890],[-1690299,366574,2002],[71890,2002]],[[0,0,0],[0,0,0],[0,0]],[[-38214774,-2490956,141466],[-2490956,584948,286],[141466,286]],[[0,0,0],[0,0],[0]],[[-122670990,-332527,139646],[-332527,516100],[139646]],[[0,0,0],[0,0],[0]],[[-256258470,5028361,77545],[5028361,266058],[77545]],[[0,0,0],[0,0],[0]],[[-362010376,9475648,24518],[9475648,79638],[24518]],[[0,0,0],[0,0],[0]],[[-341852238,9359779,4121],[9359779,12818],[4121]],[[0,0,0],[0,0],[0]],[[-191776364,5873881,286],[5873881,858],[286]],[[0,0],[0]],[[-18982600,2454530],[2454530]],[[0,0],[0]],[[73979750,682435],[682435]],[[0,0],[0]],[[78026182,121485],[121485]],[[0,0],[0]],[[45214026,12545],[12545]],[[0,0],[0]],[[17572386,572],[572]],[[0]],[[4772820]],[[0]],[[899470]],[[0]],[[112528]],[[0]],[[8424]],[[0]],[[286]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
