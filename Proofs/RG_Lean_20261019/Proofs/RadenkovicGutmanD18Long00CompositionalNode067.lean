/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode043
import Proofs.RadenkovicGutmanD18Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,2916],[0,5832,-3456],[2916,-3456,1024]],[[0,0,0],[0,0,0],[0,0]],[[0,100116,-5832],[100116,-70992,3456],[-5832,3456]],[[0,0,0],[0,0,0],[0,0]],[[695304,312660,-48924],[312660,-342456,30720],[-48924,30720]],[[0,0,0],[0,0,0],[0,0]],[[4242888,-909252,-10584],[-909252,-254320,36992],[-10584,36992]],[[0,0,0],[0,0,0],[0,0]],[[-617544,-5797512,267120],[-5797512,927328,15232],[267120,15232]],[[0,0,0],[0,0,0],[0,0]],[[-83947776,-9607620,577128],[-9607620,2288592,2048],[577128,2048]],[[0,0,0],[0,0],[0]],[[-369609920,-236140,566020],[-236140,2291592],[566020]],[[0,0,0],[0,0],[0]],[[-854744240,23032592,305848],[23032592,1240240],[305848]],[[0,0,0],[0,0],[0]],[[-1231337576,41310844,93636],[41310844,378376],[93636]],[[0,0,0],[0,0],[0]],[[-1112880200,39472820,15232],[39472820,61248],[15232]],[[0,0,0],[0,0],[0]],[[-512888576,24026632,1024],[24026632,4096],[1024]],[[0,0],[0]],[[122257640,9751380],[9751380]],[[0,0],[0]],[[410069032,2636636],[2636636]],[[0,0],[0]],[[358354736,457052],[457052]],[[0,0],[0]],[[192837088,46016],[46016]],[[0,0],[0]],[[71609664,2048],[2048]],[[0]],[[18798600]],[[0]],[[3444376]],[[0]],[[420440]],[[0]],[[30784]],[[0]],[[1024]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
