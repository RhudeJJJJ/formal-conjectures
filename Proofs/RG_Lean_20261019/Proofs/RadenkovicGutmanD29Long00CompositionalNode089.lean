/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode033
import Proofs.RadenkovicGutmanD29Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2523],[0,2523,-1566]],[[0,0,0],[0,0,0],[0,0]],[[0,-22707,22707],[-22707,83259,-17255],[22707,-17255]],[[0,0,0],[0,0,0],[0,0]],[[-213759,249777,32103],[249777,62814,-61712],[32103,-61712]],[[0,0,0],[0,0,0],[0,0]],[[41499,1228788,-237510],[1228788,-1172905,-63017],[-237510,-63017]],[[0,0,0],[0,0,0],[0,0]],[[7903602,-2371765,-885515],[-2371765,-3927238,-24215],[-885515,-24215]],[[0,0,0],[0,0,0],[0,0]],[[23612583,-26098782,-1344324],[-26098782,-5750700,-3132],[-1344324,-3132]],[[0,0,0],[0,0],[0]],[[-40368029,-76862209,-1119197],[-76862209,-4687038],[-1119197]],[[0,0,0],[0,0],[0]],[[-424910494,-127450766,-547346],[-127450766,-2257505],[-547346]],[[0,0,0],[0,0],[0]],[[-1326811944,-137379815,-156513],[-137379815,-637826],[-156513]],[[0,0,0],[0,0],[0]],[[-2504169517,-101615565,-24215],[-101615565,-97701],[-24215]],[[0,0,0],[0,0],[0]],[[-3275571692,-52627518,-1566],[-52627518,-6264],[-1566]],[[0,0],[0]],[[-3135365508,-19073010],[-19073010]],[[0,0],[0]],[[-2253609720,-4739528],[-4739528]],[[0,0],[0]],[[-1230261635,-769370],[-769370]],[[0,0],[0]],[[-510900453,-73486],[-73486]],[[0,0],[0]],[[-160248258,-3132],[-3132]],[[0]],[[-37315692]],[[0]],[[-6250167]],[[0]],[[-711515]],[[0]],[[-49271]],[[0]],[[-1566]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
