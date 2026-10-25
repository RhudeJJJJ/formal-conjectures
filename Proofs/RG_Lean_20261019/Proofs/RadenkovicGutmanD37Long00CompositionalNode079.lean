/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode033
import Proofs.RadenkovicGutmanD37Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4107],[0,4107]],[[0,0,0],[0,0,0],[0,0]],[[0,-36963,36963],[-36963,135531,17797],[36963,17797]],[[0,0,0],[0,0,0],[0,0]],[[-554445,406593,258741],[406593,928182,21904],[258741,21904]],[[0,0,0],[0,0,0],[0,0]],[[-3511485,5716944,714618],[5716944,2495687,9583],[714618,9583]],[[0,0,0],[0,0,0],[0,0]],[[1922076,25872731,1036333],[25872731,3518330,1369],[1036333,1369]],[[0,0,0],[0,0],[0]],[[90440247,64060986,870684],[64060986,2874900],[870684]],[[0,0,0],[0,0],[0]],[[429905701,100636559,436711],[100636559,1404594],[436711]],[[0,0,0],[0,0],[0]],[[1137871730,107074966,128686],[107074966,403855],[128686]],[[0,0,0],[0,0],[0]],[[2019740460,79578601,20535],[79578601,62974],[20535]],[[0,0,0],[0,0],[0]],[[2579572475,41764083,1369],[41764083,4107],[1369]],[[0,0],[0]],[[2453658700,15401250],[15401250]],[[0,0],[0]],[[1769082036,3901650],[3901650]],[[0,0],[0]],[[973950408,646168],[646168]],[[0,0],[0]],[[409173565,62974],[62974]],[[0,0],[0]],[[130072797,2738],[2738]],[[0]],[[30728574]],[[0]],[[5224104]],[[0]],[[603729]],[[0]],[[42439]],[[0]],[[1369]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
