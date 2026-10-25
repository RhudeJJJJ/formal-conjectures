/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode035
import Proofs.RadenkovicGutmanD39Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4563],[0,-4563]],[[0,0,0],[0,0,0],[0,0]],[[0,-41067,-41067],[-41067,-164268,-19773],[-41067,-19773]],[[0,0,0],[0,0,0],[0,0]],[[-739206,-1642680,-287469],[-1642680,-1149876,-24336],[-287469,-24336]],[[0,0,0],[0,0,0],[0,0]],[[-18233748,-13689000,-793962],[-13689000,-3175848,-10647],[-793962,-10647]],[[0,0,0],[0,0,0],[0,0]],[[-162953856,-54168894,-1151397],[-54168894,-4605588,-1521],[-1151397,-1521]],[[0,0,0],[0,0],[0]],[[-791388468,-126586746,-967356],[-126586746,-3869424],[-967356]],[[0,0,0],[0,0],[0]],[[-2447529318,-192449088,-485199],[-192449088,-1940796],[-485199]],[[0,0,0],[0,0],[0]],[[-5230633824,-200057130,-142974],[-200057130,-571896],[-142974]],[[0,0,0],[0,0],[0]],[[-8101539576,-145828917,-22815],[-145828917,-91260],[-22815]],[[0,0,0],[0,0],[0]],[[-9365122494,-75193677,-1521],[-75193677,-6084],[-1521]],[[0,0],[0]],[[-8226228114,-27270009],[-27270009]],[[0,0],[0]],[[-5545587294,-6798870],[-6798870]],[[0,0],[0]],[[-2878948800,-1108809],[-1108809]],[[0,0],[0]],[[-1147734432,-106470],[-106470]],[[0,0],[0]],[[-347959170,-4563],[-4563]],[[0]],[[-78720876]],[[0]],[[-12861576]],[[0]],[[-1432782]],[[0]],[[-97344]],[[0]],[[-3042]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
