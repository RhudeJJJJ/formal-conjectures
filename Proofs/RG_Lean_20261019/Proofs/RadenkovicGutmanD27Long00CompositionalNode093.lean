/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode033
import Proofs.RadenkovicGutmanD27Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,729]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,17496],[0,17496,54]],[[0,0,0],[0,0,0],[0,0]],[[-59049,-39366,98415],[-39366,380538,54918],[98415,54918]],[[0,0,0],[0,0,0],[0,0]],[[-1618380,1495908,594864],[1495908,2265732,57996],[594864,57996]],[[0,0,0],[0,0,0],[0,0]],[[-6945183,14670396,1492992],[14670396,5585598,24246],[1492992,24246]],[[0,0,0],[0,0,0],[0,0]],[[16686810,58653882,2030994],[58653882,7456212,3780],[2030994,3780]],[[0,0,0],[0,0,0],[0,0]],[[239155821,135042876,1637982],[135042876,5904576,108],[1637982,108]],[[0,0,0],[0,0],[0]],[[991559340,201912588,804546],[201912588,2853684],[804546]],[[0,0,0],[0,0],[0]],[[2445851322,207409248,237384],[207409248,831438],[237384]],[[0,0,0],[0,0],[0]],[[4143010464,150422346,39366],[150422346,137052],[39366]],[[0,0,0],[0,0],[0]],[[5114788146,77771286,3051],[77771286,10746],[3051]],[[0,0,0],[0,0],[0]],[[4743581076,28538082,54],[28538082,216],[54]],[[0,0],[0]],[[3357302688,7286760],[7286760]],[[0,0],[0]],[[1825331544,1241460],[1241460]],[[0,0],[0]],[[761895369,129924],[129924]],[[0,0],[0]],[[242287524,6966],[6966]],[[0,0],[0]],[[57768066,108],[108]],[[0]],[[10043352]],[[0]],[[1214649]],[[0]],[[93960]],[[0]],[[3915]],[[0]],[[54]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
