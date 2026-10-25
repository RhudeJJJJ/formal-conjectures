/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode043
import Proofs.RadenkovicGutmanD24Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-5184],[0,-10368,3168],[-5184,3168]],[[0,0,0],[0,0,0],[0,0]],[[0,-204768,-16416],[-204768,14688,13728],[-16416,13728]],[[0,0,0],[0,0,0],[0,0]],[[-1905120,-1666656,46944],[-1666656,410688,16896],[46944,16896]],[[0,0,0],[0,0,0],[0,0]],[[-23029920,-5104512,287424],[-5104512,1397472,7392],[287424,7392]],[[0,0,0],[0,0,0],[0,0]],[[-123254784,-5958816,543648],[-5958816,2202432,1056],[543648,1056]],[[0,0,0],[0,0],[0]],[[-385051680,4630464,527616],[4630464,1929600],[527616]],[[0,0,0],[0,0],[0]],[[-774194592,25673568,290208],[25673568,990144],[290208]],[[0,0,0],[0,0],[0]],[[-1028363712,40934592,91200],[40934592,295392],[91200]],[[0,0,0],[0,0],[0]],[[-857023488,38029728,15264],[38029728,47424],[15264]],[[0,0,0],[0,0],[0]],[[-309012384,23095008,1056],[23095008,3168],[1056]],[[0,0],[0]],[[228129408,9450816],[9450816]],[[0,0],[0]],[[443111040,2589120],[2589120]],[[0,0],[0]],[[361860480,455808],[455808]],[[0,0],[0]],[[191115936,46656],[46656]],[[0,0],[0]],[[70756704,2112],[2112]],[[0]],[[18648000]],[[0]],[[3442560]],[[0]],[[424224]],[[0]],[[31392]],[[0]],[[1056]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
