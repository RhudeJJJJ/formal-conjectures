/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode035
import Proofs.RadenkovicGutmanD37Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4107],[0,-4107]],[[0,0,0],[0,0,0],[0,0]],[[0,-36963,-36963],[-36963,-147852,-17797],[-36963,-17797]],[[0,0,0],[0,0,0],[0,0]],[[-665334,-1478520,-258741],[-1478520,-1034964,-21904],[-258741,-21904]],[[0,0,0],[0,0,0],[0,0]],[[-16411572,-12321000,-714618],[-12321000,-2858472,-9583],[-714618,-9583]],[[0,0,0],[0,0,0],[0,0]],[[-146669184,-48755566,-1036333],[-48755566,-4145332,-1369],[-1036333,-1369]],[[0,0,0],[0,0],[0]],[[-712301652,-113936394,-870684],[-113936394,-3482736],[-870684]],[[0,0,0],[0,0],[0]],[[-2202937302,-173216832,-436711],[-173216832,-1746844],[-436711]],[[0,0,0],[0,0],[0]],[[-4707914336,-180064570,-128686],[-180064570,-514744],[-128686]],[[0,0,0],[0,0],[0]],[[-7291918264,-131255613,-20535],[-131255613,-82140],[-20535]],[[0,0,0],[0,0],[0]],[[-8429225966,-67679253,-1369],[-67679253,-5476],[-1369]],[[0,0],[0]],[[-7404146146,-24544801],[-24544801]],[[0,0],[0]],[[-4991393166,-6119430],[-6119430]],[[0,0],[0]],[[-2591243200,-998001],[-998001]],[[0,0],[0]],[[-1033036448,-95830],[-95830]],[[0,0],[0]],[[-313186130,-4107],[-4107]],[[0]],[[-70853964]],[[0]],[[-11576264]],[[0]],[[-1289598]],[[0]],[[-87616]],[[0]],[[-2738]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
