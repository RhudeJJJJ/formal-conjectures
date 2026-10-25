/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode035
import Proofs.RadenkovicGutmanD20Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1200],[0,-1200]],[[0,0,0],[0,0,0],[0,0]],[[0,-10800,-10800],[-10800,-43200,-5200],[-10800,-5200]],[[0,0,0],[0,0,0],[0,0]],[[-194400,-432000,-75600],[-432000,-302400,-6400],[-75600,-6400]],[[0,0,0],[0,0,0],[0,0]],[[-4795200,-3600000,-208800],[-3600000,-835200,-2800],[-208800,-2800]],[[0,0,0],[0,0,0],[0,0]],[[-42854400,-14245600,-302800],[-14245600,-1211200,-400],[-302800,-400]],[[0,0,0],[0,0],[0]],[[-208123200,-33290400,-254400],[-33290400,-1017600],[-254400]],[[0,0,0],[0,0],[0]],[[-643663200,-50611200,-127600],[-50611200,-510400],[-127600]],[[0,0,0],[0,0],[0]],[[-1375577600,-52612000,-37600],[-52612000,-150400],[-37600]],[[0,0,0],[0,0],[0]],[[-2130582400,-38350800,-6000],[-38350800,-24000],[-6000]],[[0,0,0],[0,0],[0]],[[-2462885600,-19774800,-400],[-19774800,-1600],[-400]],[[0,0],[0]],[[-2163373600,-7171600],[-7171600]],[[0,0],[0]],[[-1458405600,-1788000],[-1788000]],[[0,0],[0]],[[-757120000,-291600],[-291600]],[[0,0],[0]],[[-301836800,-28000],[-28000]],[[0,0],[0]],[[-91508000,-1200],[-1200]],[[0]],[[-20702400]],[[0]],[[-3382400]],[[0]],[[-376800]],[[0]],[[-25600]],[[0]],[[-800]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
