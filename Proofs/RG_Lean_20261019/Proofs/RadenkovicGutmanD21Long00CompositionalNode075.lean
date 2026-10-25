/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode033
import Proofs.RadenkovicGutmanD21Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,441]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,7938],[0,7938]],[[0,0,0],[0,0,0],[0,0]],[[-35721,0,35721],[0,142884,21168],[35721,21168]],[[0,0,0],[0,0,0],[0,0]],[[-619164,642978,190512],[642978,762048,19404],[190512,19404]],[[0,0,0],[0,0,0],[0,0]],[[-1893213,5143824,428652],[5143824,1714608,7056],[428652,7056]],[[0,0,0],[0,0,0],[0,0]],[[8996400,18432036,529200],[18432036,2116800,882],[529200,882]],[[0,0,0],[0,0],[0]],[[85740543,39054960,390726],[39054960,1562904],[390726]],[[0,0,0],[0,0],[0]],[[316507464,54414990,176400],[54414990,705600],[176400]],[[0,0,0],[0,0],[0]],[[723052134,52454304,47628],[52454304,190512],[47628]],[[0,0,0],[0,0],[0]],[[1151456292,35840952,7056],[35840952,28224],[7056]],[[0,0,0],[0,0],[0]],[[1346907492,17484768,441],[17484768,1764],[441]],[[0,0],[0]],[[1188994212,6046110],[6046110]],[[0,0],[0]],[[803128032,1446480],[1446480]],[[0,0],[0]],[[417238920,227556],[227556]],[[0,0],[0]],[[166376511,21168],[21168]],[[0,0],[0]],[[50443344,882],[882]],[[0]],[[11412198]],[[0]],[[1864548]],[[0]],[[207711]],[[0]],[[14112]],[[0]],[[441]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
