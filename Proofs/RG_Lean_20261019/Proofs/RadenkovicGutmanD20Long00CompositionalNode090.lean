/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode035
import Proofs.RadenkovicGutmanD20Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1200],[0,-1200]],[[0,0,0],[0,0,0],[0,0]],[[0,-10800,-18000],[-10800,-57600,-5320],[-18000,-5320]],[[0,0,0],[0,0,0],[0,0]],[[-194400,-670680,-139080],[-670680,-431520,-6920],[-139080,-6920]],[[0,0,0],[0,0,0],[0,0]],[[-6758640,-6300000,-428360],[-6300000,-1289440,-3440],[-428360,-3440]],[[0,0,0],[0,0,0],[0,0]],[[-69901920,-27299200,-690080],[-27299200,-2027520,-680],[-690080,-680]],[[0,0,0],[0,0,0],[0,0]],[[-374365440,-69074960,-639880],[-69074960,-1849120,-40],[-639880,-40]],[[0,0,0],[0,0],[0]],[[-1250728320,-112918640,-353040],[-112918640,-1012160],[-353040]],[[0,0,0],[0,0],[0]],[[-2854820720,-125622720,-115160],[-125622720,-331040],[-115160]],[[0,0,0],[0,0],[0]],[[-4689032960,-97720800,-20960],[-97720800,-61440],[-20960]],[[0,0,0],[0,0],[0]],[[-5721068640,-53737080,-1800],[-53737080,-5600],[-1800]],[[0,0,0],[0,0],[0]],[[-5288028560,-20836280,-40],[-20836280,-160],[-40]],[[0,0],[0]],[[-3744925360,-5597960],[-5597960]],[[0,0],[0]],[[-2041662960,-1002400],[-1002400]],[[0,0],[0]],[[-855803200,-110760],[-110760]],[[0,0],[0]],[[-273714080,-6400],[-6400]],[[0,0],[0]],[[-65766800,-120],[-120]],[[0]],[[-11558240]],[[0]],[[-1420640]],[[0]],[[-112880]],[[0]],[[-4960]],[[0]],[[-80]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
