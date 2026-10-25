/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1369]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-24642,24642],[0,24642]],[[0,0,0],[0,0,0],[0,0]],[[110889,-221778,110889],[-221778,229992,65712],[110889,65712]],[[0,0,0],[0,0,0],[0,0]],[[-73926,-517482,591408],[-517482,1640062,60236],[591408,60236]],[[0,0,0],[0,0,0],[0,0]],[[-4102893,3770226,1330668],[3770226,4068668,21904],[1330668,21904]],[[0,0,0],[0,0,0],[0,0]],[[-11294250,23623464,1642800],[23623464,5355528,2738],[1642800,2738]],[[0,0,0],[0,0],[0]],[[23772685,62505802,1212934],[62505802,4167236],[1212934]],[[0,0,0],[0,0],[0]],[[225561916,99978070,547600],[99978070,1968622],[547600]],[[0,0,0],[0,0],[0]],[[704725606,106907948,147852],[106907948,553076],[147852]],[[0,0,0],[0,0],[0]],[[1355055366,79555328,21904],[79555328,84878],[21904]],[[0,0,0],[0,0],[0]],[[1823759896,41762714,1369],[41762714,5476],[1369]],[[0,0],[0]],[[1808492808,15401250],[15401250]],[[0,0],[0]],[[1353218168,3901650],[3901650]],[[0,0],[0]],[[771636850,646168],[646168]],[[0,0],[0]],[[335455653,62974],[62974]],[[0,0],[0]],[[110292116,2738],[2738]],[[0]],[[26939182]],[[0]],[[4734002]],[[0]],[[565397]],[[0]],[[41070]],[[0]],[[1369]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
