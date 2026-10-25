/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode100
import Proofs.RadenkovicGutmanD45Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,2025]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-18225],[0,-36450,60210],[-18225,60210,90]],[[0,0,0],[0,0,0],[0,0]],[[-164025,-606285,219915],[-606285,1162350,201780],[219915,201780]],[[0,0,0],[0,0,0],[0,0]],[[-7501410,1639035,1842345],[1639035,8154810,220140],[1842345,220140]],[[0,0,0],[0,0,0],[0,0]],[[-39296745,43693425,5213970],[43693425,21732930,91800],[5213970,91800]],[[0,0,0],[0,0,0],[0,0]],[[58854600,214683840,7613820],[214683840,30563460,13410],[7613820,13410]],[[0,0,0],[0,0,0],[0,0]],[[1233594765,549824085,6433020],[549824085,25106220,180],[6433020,180]],[[0,0,0],[0,0],[0]],[[5528329920,880942995,3252195],[880942995,12414330],[3252195]],[[0,0,0],[0,0],[0]],[[14259209670,949856400,970830],[949856400,3641130],[970830]],[[0,0,0],[0,0],[0]],[[24867454770,712841085,158895],[712841085,587970],[158895]],[[0,0,0],[0,0],[0]],[[31282959240,377061795,11385],[377061795,41850],[11385]],[[0,0,0],[0,0],[0]],[[29333129760,140095710,90],[140095710,360],[90]],[[0,0],[0]],[[20858040450,35813475],[35813475]],[[0,0],[0]],[[11331936270,6014655],[6014655]],[[0,0],[0]],[[4702688325,602685],[602685]],[[0,0],[0]],[[1479023640,28440],[28440]],[[0,0],[0]],[[346525290,180],[180]],[[0]],[[58657950]],[[0]],[[6799095]],[[0]],[[487530]],[[0]],[[17055]],[[0]],[[90]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
