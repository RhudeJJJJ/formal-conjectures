/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode071
import Proofs.RadenkovicGutmanD36Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-69984,0],[-69984,-14256,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1178064,-1318032,0],[-1318032,-170856,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-24099768,-10581192,0],[-10581192,-829728,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-218690280,-48019392,0],[-48019392,-2118312,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1171018512,-137720952,0],[-137720952,-3110544,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4153168152,-264634848,0],[-264634848,-2729664,0],[0,0]],[[0,0,0],[0,0],[0]],[[-10383479352,-352733976,0],[-352733976,-1442304],[0]],[[0,0,0],[0,0],[0]],[[-19016872560,-333007200,0],[-333007200,-447912],[0]],[[0,0,0],[0,0],[0]],[[-26163782640,-225024624,0],[-225024624,-75168],[0]],[[0,0,0],[0,0],[0]],[[-27494712216,-108939312,0],[-108939312,-5256],[0]],[[0,0,0],[0,0],[0]],[[-22299367248,-37406808,0],[-37406808,0],[0]],[[0,0],[0]],[[-14031271728,-8881632],[-8881632]],[[0,0],[0]],[[-6852157200,-1385208],[-1385208]],[[0,0],[0]],[[-2584621512,-127584],[-127584]],[[0,0],[0]],[[-744687576,-5256],[-5256]],[[0,0],[0]],[[-160671600,0],[0]],[[0]],[[-25104816]],[[0]],[[-2680632]],[[0]],[[-174888]],[[0]],[[-5256]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
