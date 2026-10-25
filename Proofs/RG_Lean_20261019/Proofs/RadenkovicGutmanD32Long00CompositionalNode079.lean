/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode033
import Proofs.RadenkovicGutmanD32Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3072],[0,3072]],[[0,0,0],[0,0,0],[0,0]],[[0,-27648,27648],[-27648,101376,13312],[27648,13312]],[[0,0,0],[0,0,0],[0,0]],[[-414720,304128,193536],[304128,694272,16384],[193536,16384]],[[0,0,0],[0,0,0],[0,0]],[[-2626560,4276224,534528],[4276224,1866752,7168],[534528,7168]],[[0,0,0],[0,0,0],[0,0]],[[1437696,19352576,775168],[19352576,2631680,1024],[775168,1024]],[[0,0,0],[0,0],[0]],[[67648512,47917056,651264],[47917056,2150400],[651264]],[[0,0,0],[0,0],[0]],[[321565696,75275264,326656],[75275264,1050624],[326656]],[[0,0,0],[0,0],[0]],[[851118080,80091136,96256],[80091136,302080],[96256]],[[0,0,0],[0,0],[0]],[[1510748160,59524096,15360],[59524096,47104],[15360]],[[0,0,0],[0,0],[0]],[[1929497600,31239168,1024],[31239168,3072],[1024]],[[0,0],[0]],[[1835315200,11520000],[11520000]],[[0,0],[0]],[[1323257856,2918400],[2918400]],[[0,0],[0]],[[728506368,483328],[483328]],[[0,0],[0]],[[306058240,47104],[47104]],[[0,0],[0]],[[97293312,2048],[2048]],[[0]],[[22984704]],[[0]],[[3907584]],[[0]],[[451584]],[[0]],[[31744]],[[0]],[[1024]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
