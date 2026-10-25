/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode073
import Proofs.RadenkovicGutmanD40Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2880,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25920,-371520,0],[-371520,-83280,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6391440,-5311440,0],[-5311440,-590240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-100049040,-32372640,0],[-32372640,-1863760,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-714687360,-111258800,0],[-111258800,-3109920,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3040362320,-241010720,0],[-241010720,-2957120,0],[0,0]],[[0,0,0],[0,0],[0]],[[-8610887280,-349082480,0],[-349082480,-1645920],[0]],[[0,0,0],[0,0],[0]],[[-17253226720,-349773120,0],[-349773120,-529360],[0]],[[0,0,0],[0,0],[0]],[[-25382551680,-246926880,0],[-246926880,-91040],[0]],[[0,0,0],[0,0],[0]],[[-28077128240,-123541120,0],[-123541120,-6480],[0]],[[0,0,0],[0,0],[0]],[[-23701971680,-43504880,0],[-43504880,0],[0]],[[0,0],[0]],[[-15395544800,-10535200],[-10535200]],[[0,0],[0]],[[-7713365440,-1669040],[-1669040]],[[0,0],[0]],[[-2970844080,-155680],[-155680]],[[0,0],[0]],[[-870828720,-6480],[-6480]],[[0,0],[0]],[[-190600800,0],[0]],[[0]],[[-30142400]],[[0]],[[-3251600]],[[0]],[[-214000]],[[0]],[[-6480]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
