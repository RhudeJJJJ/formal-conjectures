/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode033
import Proofs.RadenkovicGutmanD17Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,867],[0,867]],[[0,0,0],[0,0,0],[0,0]],[[0,-7803,7803],[-7803,28611,3757],[7803,3757]],[[0,0,0],[0,0,0],[0,0]],[[-117045,85833,54621],[85833,195942,4624],[54621,4624]],[[0,0,0],[0,0,0],[0,0]],[[-741285,1206864,150858],[1206864,526847,2023],[150858,2023]],[[0,0,0],[0,0,0],[0,0]],[[405756,5461811,218773],[5461811,742730,289],[218773,289]],[[0,0,0],[0,0],[0]],[[19092207,13523466,183804],[13523466,606900],[183804]],[[0,0,0],[0,0],[0]],[[90754381,21244679,92191],[21244679,296514],[92191]],[[0,0,0],[0,0],[0]],[[240208130,22603846,27166],[22603846,85255],[27166]],[[0,0,0],[0,0],[0]],[[426373260,16799281,4335],[16799281,13294],[4335]],[[0,0,0],[0,0],[0]],[[544555475,8816523,289],[8816523,867],[289]],[[0,0],[0]],[[517974700,3251250],[3251250]],[[0,0],[0]],[[373458516,823650],[823650]],[[0,0],[0]],[[205603848,136408],[136408]],[[0,0],[0]],[[86377765,13294],[13294]],[[0,0],[0]],[[27458757,578],[578]],[[0]],[[6486894]],[[0]],[[1102824]],[[0]],[[127449]],[[0]],[[8959]],[[0]],[[289]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
