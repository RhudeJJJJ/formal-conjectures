/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode033
import Proofs.RadenkovicGutmanD18Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,324]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,5832],[0,5832]],[[0,0,0],[0,0,0],[0,0]],[[-26244,0,26244],[0,104976,15552],[26244,15552]],[[0,0,0],[0,0,0],[0,0]],[[-454896,472392,139968],[472392,559872,14256],[139968,14256]],[[0,0,0],[0,0,0],[0,0]],[[-1390932,3779136,314928],[3779136,1259712,5184],[314928,5184]],[[0,0,0],[0,0,0],[0,0]],[[6609600,13541904,388800],[13541904,1555200,648],[388800,648]],[[0,0,0],[0,0],[0]],[[62993052,28693440,287064],[28693440,1148256],[287064]],[[0,0,0],[0,0],[0]],[[232536096,39978360,129600],[39978360,518400],[129600]],[[0,0,0],[0,0],[0]],[[531221976,38537856,34992],[38537856,139968],[34992]],[[0,0,0],[0,0],[0]],[[845967888,26332128,5184],[26332128,20736],[5184]],[[0,0,0],[0,0],[0]],[[989564688,12845952,324],[12845952,1296],[324]],[[0,0],[0]],[[873546768,4442040],[4442040]],[[0,0],[0]],[[590053248,1062720],[1062720]],[[0,0],[0]],[[306542880,167184],[167184]],[[0,0],[0]],[[122235804,15552],[15552]],[[0,0],[0]],[[37060416,648],[648]],[[0]],[[8384472]],[[0]],[[1369872]],[[0]],[[152604]],[[0]],[[10368]],[[0]],[[324]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
