/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode089
import Proofs.RadenkovicGutmanD39Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,9126],[0,9126,-2886]],[[0,0,0],[0,0,0],[0,0]],[[0,0,109512],[0,369603,-12168],[109512,-12168]],[[0,0,0],[0,0,0],[0,0]],[[356967,2999997,580554],[2999997,1729026,-88842],[580554,-88842]],[[0,0,0],[0,0,0],[0,0]],[[25814295,26019630,1162044],[26019630,2632851,-104442],[1162044,-104442]],[[0,0,0],[0,0,0],[0,0]],[[279438822,98221383,931554],[98221383,243126,-42588],[931554,-42588]],[[0,0,0],[0,0,0],[0,0]],[[1457193231,210568956,-118794],[210568956,-3851796,-5694],[-118794,-5694]],[[0,0,0],[0,0],[0]],[[4633872945,279432153,-776490],[279432153,-5007210],[-776490]],[[0,0,0],[0,0],[0]],[[9929133006,231164622,-597168],[231164622,-3004677],[-597168]],[[0,0,0],[0,0],[0]],[[15087403656,106978794,-216138],[106978794,-971022],[-216138]],[[0,0,0],[0,0],[0]],[[16690274757,9080916,-38922],[9080916,-163293],[-38922]],[[0,0,0],[0,0],[0]],[[13563111510,-21746205,-2808],[-21746205,-11232],[-2808]],[[0,0],[0]],[[8023779894,-15274506],[-15274506]],[[0,0],[0]],[[3319497168,-5267769],[-5267769]],[[0,0],[0]],[[838036953,-1052064],[-1052064]],[[0,0],[0]],[[40593189,-116337],[-116337]],[[0,0],[0]],[[-62845458,-5538],[-5538]],[[0]],[[-28764684]],[[0]],[[-6755853]],[[0]],[[-952731]],[[0]],[[-76713]],[[0]],[[-2730]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
