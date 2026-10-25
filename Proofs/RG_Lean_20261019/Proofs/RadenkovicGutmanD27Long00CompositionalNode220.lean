/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode217
import Proofs.RadenkovicGutmanD27Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-1458],[0],[0]],[[0,0],[0,0],[0]],[[-45198,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-642978,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-5563728,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-32726268,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-138530412,-2187,0],[-2187,0],[0]],[[0,0,0],[0,0],[0]],[[-435809322,-48843,0],[-48843,0],[0]],[[0,0,0],[0,0],[0]],[[-1037642562,-484785,0],[-484785,0],[0]],[[0,0,0],[0,0],[0]],[[-1886453712,-2818314,0],[-2818314,0],[0]],[[0,0,0],[0,0],[0]],[[-2622911382,-10649961,0],[-10649961,0],[0]],[[0,0,0],[0,0],[0]],[[-2774869974,-27453411,-729],[-27453411,-1458],[-729]],[[0,0,0],[0,0],[0]],[[-2206038564,-49306644,-10206],[-49306644,-20412],[-10206]],[[0,0,0],[0,0],[0]],[[-1289306484,-61919073,-59049],[-61919073,-118098],[-59049]],[[0,0,0],[0,0],[0]],[[-534222864,-53744067,-182250],[-53744067,-364500],[-182250]],[[0,0,0],[0,0],[0]],[[-147583134,-31310550,-323676],[-31310550,-647352],[-323676]],[[0,0,0],[0,0],[0]],[[-24210090,-11567043,-333882],[-11567043,-667764],[-333882]],[[0,0,0],[0,0],[0]],[[-1771470,-2421009,-193185],[-2421009,-386370],[-193185]],[[0,0,0],[0,0],[0]],[[0,-216513,-56862],[-216513,-113724],[-56862]],[[0,0,0],[0,0],[0]],[[0,0,-6561],[0,-13122],[-6561]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
