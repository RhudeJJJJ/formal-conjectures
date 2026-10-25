/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode043
import Proofs.RadenkovicGutmanD37Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,12321],[0,24642,-15540],[12321,-15540,4900]],[[0,0,0],[0,0,0],[0,0]],[[0,414585,-33078],[414585,-327606,20860],[-33078,20860]],[[0,0,0],[0,0,0],[0,0]],[[2794500,1038555,-219335],[1038555,-1444570,152320],[-219335,152320]],[[0,0,0],[0,0,0],[0,0]],[[14823000,-5195709,39842],[-5195709,-556686,179340],[39842,179340]],[[0,0,0],[0,0,0],[0,0]],[[-24267870,-25916840,1449376],[-25916840,5511572,73220],[1449376,73220]],[[0,0,0],[0,0,0],[0,0]],[[-428640570,-34319837,2927770],[-34319837,11927900,9800],[2927770,9800]],[[0,0,0],[0,0],[0]],[[-1690098786,24780951,2799869],[24780951,11485198],[2799869]],[[0,0,0],[0,0],[0]],[[-3658052728,144031052,1492246],[144031052,6095082],[1492246]],[[0,0,0],[0,0],[0]],[[-4887510730,226630327,452869],[226630327,1837158],[452869]],[[0,0,0],[0,0],[0]],[[-3831164600,205780561,73220],[205780561,294910],[73220]],[[0,0,0],[0,0],[0]],[[-883388196,121746368,4900],[121746368,19600],[4900]],[[0,0],[0]],[[1800994470,48499505],[48499505]],[[0,0],[0]],[[2667911194,12938949],[12938949]],[[0,0],[0]],[[2023432390,2220043],[2220043]],[[0,0],[0]],[[1024012494,221690],[221690]],[[0,0],[0]],[[367192740,9800],[9800]],[[0]],[[94210170]],[[0]],[[16982028]],[[0]],[[2047524]],[[0]],[[148470]],[[0]],[[4900]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
