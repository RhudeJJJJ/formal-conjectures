/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,900],[0,1800,-960],[900,-960,256]],[[0,0,0],[0,0,0],[0,0]],[[0,45360,-840],[45360,-25872,448],[-840,448]],[[0,0,0],[0,0,0],[0,0]],[[571536,240192,-13244],[240192,-165880,7168],[-13244,7168]],[[0,0,0],[0,0,0],[0,0]],[[6586272,132624,-10648],[132624,-337712,9024],[-10648,9024]],[[0,0,0],[0,0,0],[0,0]],[[33925392,-2019936,50992],[-2019936,-236576,3776],[50992,3776]],[[0,0,0],[0,0,0],[0,0]],[[102141216,-7110704,128680],[-7110704,123728,512],[128680,512]],[[0,0,0],[0,0],[0]],[[196259616,-11593568,132836],[-11593568,323144],[132836]],[[0,0,0],[0,0],[0]],[[242895840,-10415200,73720],[-10415200,229872],[73720]],[[0,0,0],[0,0],[0]],[[174979312,-4357344,22948],[-4357344,80840],[22948]],[[0,0,0],[0,0],[0]],[[28753248,860752,3776],[860752,14336],[3776]],[[0,0,0],[0,0],[0]],[[-81341408,2237280,256],[2237280,1024],[256]],[[0,0],[0]],[[-92974880,1376720],[1376720]],[[0,0],[0]],[[-45727760,466880],[466880]],[[0,0],[0]],[[-4669728,94000],[94000]],[[0,0],[0]],[[8449056,10560],[10560]],[[0,0],[0]],[[6253856,512],[512]],[[0]],[[2342160]],[[0]],[[545440]],[[0]],[[79888]],[[0]],[[6784]],[[0]],[[256]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
