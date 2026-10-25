/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode100
import Proofs.RadenkovicGutmanD9Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,81]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-729],[0,-1458,2322],[-729,2322,18]],[[0,0,0],[0,0,0],[0,0]],[[-6561,-25029,8019],[-25029,43902,7956],[8019,7956]],[[0,0,0],[0,0,0],[0,0]],[[-310554,39123,69417],[39123,313578,9036],[69417,9036]],[[0,0,0],[0,0,0],[0,0]],[[-1814481,1562409,199746],[1562409,849330,4104],[199746,4104]],[[0,0,0],[0,0,0],[0,0]],[[419904,7986240,296748],[7986240,1217700,738],[296748,738]],[[0,0,0],[0,0,0],[0,0]],[[41189877,20904669,256284],[20904669,1025676,36],[256284,36]],[[0,0,0],[0,0],[0]],[[199929816,34104555,133659],[34104555,525258],[133659]],[[0,0,0],[0,0],[0]],[[534047670,37433376,41886],[37433376,162522],[41886]],[[0,0,0],[0,0],[0]],[[953234802,28641717,7479],[28641717,28818],[7479]],[[0,0,0],[0,0],[0]],[[1221880680,15496011,657],[15496011,2538],[657]],[[0,0,0],[0,0],[0]],[[1165427424,5921694,18],[5921694,72],[18]],[[0,0],[0]],[[842738130,1572075],[1572075]],[[0,0],[0]],[[465995070,279207],[279207]],[[0,0],[0]],[[197217837,30789],[30789]],[[0,0],[0]],[[63477936,1800],[1800]],[[0,0],[0]],[[15310458,36],[36]],[[0]],[[2695230]],[[0]],[[331119]],[[0]],[[26226]],[[0]],[[1143]],[[0]],[[18]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
