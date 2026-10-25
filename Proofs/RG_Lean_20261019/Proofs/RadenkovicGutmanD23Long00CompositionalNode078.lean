/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode075
import Proofs.RadenkovicGutmanD23Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,529]],[[0,0],[0,0,0],[0,0]],[[0,0,4761],[0,9522,9522],[4761,9522]],[[0,0,0],[0,0,0],[0,0]],[[-42849,157113,84111],[157113,253920,25392],[84111,25392]],[[0,0,0],[0,0,0],[0,0]],[[542754,2528091,368713],[2528091,1194482,23276],[368713,23276]],[[0,0,0],[0,0,0],[0,0]],[[15297093,14563899,756470],[14563899,2541316,8464],[756470,8464]],[[0,0,0],[0,0,0],[0,0]],[[117885534,44830634,869676],[44830634,3008952,1058],[869676,1058]],[[0,0,0],[0,0],[0]],[[490509431,85847707,600944],[85847707,2139276],[600944]],[[0,0,0],[0,0],[0]],[[1315252700,110204983,254449],[110204983,932098],[254449]],[[0,0,0],[0,0],[0]],[[2468150010,98700820,64538],[98700820,243340],[64538]],[[0,0,0],[0,0],[0]],[[3394814122,62914499,8993],[62914499,34914],[8993]],[[0,0,0],[0,0],[0]],[[3518997930,28701953,529],[28701953,2116],[529]],[[0,0],[0]],[[2795161940,9297704],[9297704]],[[0,0],[0]],[[1716356370,2086905],[2086905]],[[0,0],[0]],[[816743202,308407],[308407]],[[0,0],[0]],[[300101171,26979],[26979]],[[0,0],[0]],[[84257004,1058],[1058]],[[0]],[[17726790]],[[0]],[[2703190]],[[0]],[[281957]],[[0]],[[17986]],[[0]],[[529]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
