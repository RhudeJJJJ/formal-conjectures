/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode092
import Proofs.RadenkovicGutmanD33Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2376,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21384,-21384,0],[-21384,-19998,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-557766,-237006,0],[-237006,-64812,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5419062,-1115532,0],[-1115532,-103422,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-28572192,-2945250,0],[-2945250,-86988,0],[0,0]],[[0,0,0],[0,0],[0]],[[-94904238,-4853244,0],[-4853244,-36696],[0]],[[0,0,0],[0,0],[0]],[[-214503498,-5231754,0],[-5231754,-4884],[0]],[[0,0,0],[0,0],[0]],[[-344814228,-3730584,0],[-3730584,1650],[0]],[[0,0,0],[0,0],[0]],[[-404292768,-1709004,0],[-1709004,660],[0]],[[0,0,0],[0,0],[0]],[[-349761522,-442464,0],[-442464,66],[0]],[[0,0],[0]],[[-222870516,-23034],[-23034]],[[0,0],[0]],[[-102466452,24420],[24420]],[[0,0],[0]],[[-31932120,8382],[8382]],[[0,0],[0]],[[-5354514,1188],[1188]],[[0,0],[0]],[[345246,66],[66]],[[0]],[[474012]],[[0]],[[135432]],[[0]],[[20922]],[[0]],[[1782]],[[0]],[[66]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
