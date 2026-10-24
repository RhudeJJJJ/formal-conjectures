/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode034
import Proofs.RadenkovicGutmanD4Long00CompositionalNode073
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e034 e073
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-144],[0,-288],[-144]],[[0,0,0],[0,0],[0]],[[0,-4752,-1248],[-4752,-2496],[-1248]],[[0,0,0],[0,0],[0]],[[-38880,-53136,-4240],[-53136,-8480],[-4240]],[[0,0,0],[0,0],[0]],[[-531360,-253872,-7328],[-253872,-14656],[-7328]],[[0,0,0],[0,0],[0]],[[-3239136,-687200,-7104],[-687200,-14208],[-7104]],[[0,0,0],[0,0],[0]],[[-11725056,-1179568,-4000],[-1179568,-8000],[-4000]],[[0,0,0],[0,0],[0]],[[-28297536,-1358992,-1296],[-1358992,-2592],[-1296]],[[0,0,0],[0,0],[0]],[[-48417856,-1082176,-224],[-1082176,-448],[-224]],[[0,0,0],[0,0],[0]],[[-60902496,-602544,-16],[-602544,-32],[-16]],[[0,0],[0]],[[-57567328,-233744],[-233744]],[[0,0],[0]],[[-41403648,-61856],[-61856]],[[0,0],[0]],[[-22774048,-10640],[-10640]],[[0,0],[0]],[[-9565088,-1072],[-1072]],[[0,0],[0]],[[-3040448,-48],[-48]],[[0]],[[-718272]],[[0]],[[-122112]],[[0]],[[-14112]],[[0]],[[-992]],[[0]],[[-32]]]
theorem step075 : p075=NestedArithmetic.mul p034 p073 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e034 e073 p034 p073 p075 rfl h034 h073 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
