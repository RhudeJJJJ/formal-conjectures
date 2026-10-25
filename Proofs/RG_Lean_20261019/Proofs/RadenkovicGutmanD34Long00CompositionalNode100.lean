/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode043
import Proofs.RadenkovicGutmanD34Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-10404],[0,-20808,6528],[-10404,6528]],[[0,0,0],[0,0,0],[0,0]],[[0,-409428,-31416],[-409428,35088,28288],[-31416,28288]],[[0,0,0],[0,0,0],[0,0]],[[-3800520,-3288276,104924],[-3288276,862648,34816],[104924,34816]],[[0,0,0],[0,0,0],[0,0]],[[-45661320,-9786492,606424],[-9786492,2907952,15232],[606424,15232]],[[0,0,0],[0,0,0],[0,0]],[[-242487864,-10193336,1133968],[-10193336,4565792,2176],[1133968,2176]],[[0,0,0],[0,0],[0]],[[-749724480,13313924,1094936],[13313924,3991600],[1094936]],[[0,0,0],[0,0],[0]],[[-1484558592,57479788,600508],[57479788,2045304],[600508]],[[0,0,0],[0,0],[0]],[[-1920532432,88179952,188360],[88179952,609552],[188360]],[[0,0,0],[0,0],[0]],[[-1505063448,80599108,31484],[80599108,97784],[31484]],[[0,0,0],[0,0],[0]],[[-379766264,48495628,2176],[48495628,6528],[2176]],[[0,0],[0]],[[662119808,19724216],[19724216]],[[0,0],[0]],[[1022518040,5379820],[5379820]],[[0,0],[0]],[[793151320,943908],[943908]],[[0,0],[0]],[[409379856,96356],[96356]],[[0,0],[0]],[[149584224,4352],[4352]],[[0]],[[39086400]],[[0]],[[7171960]],[[0]],[[879784]],[[0]],[[64872]],[[0]],[[2176]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
