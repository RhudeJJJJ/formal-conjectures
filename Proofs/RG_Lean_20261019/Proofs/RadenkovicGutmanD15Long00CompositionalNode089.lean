/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode033
import Proofs.RadenkovicGutmanD15Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,675],[0,675,-390]],[[0,0,0],[0,0,0],[0,0]],[[0,-6075,6075],[-6075,22275,-4095],[6075,-4095]],[[0,0,0],[0,0,0],[0,0]],[[-59535,66825,10935],[66825,26190,-15120],[10935,-15120]],[[0,0,0],[0,0,0],[0,0]],[[-29565,370980,-51030],[370980,-263745,-15585],[-51030,-15585]],[[0,0,0],[0,0,0],[0,0]],[[1990170,-296685,-208755],[-296685,-938070,-6015],[-208755,-6015]],[[0,0,0],[0,0,0],[0,0]],[[6908175,-5771790,-324900],[-5771790,-1399500,-780],[-324900,-780]],[[0,0,0],[0,0],[0]],[[-5168445,-17998425,-273765],[-17998425,-1151310],[-273765]],[[0,0,0],[0,0],[0]],[[-92891310,-30523950,-134850],[-30523950,-557625],[-134850]],[[0,0,0],[0,0],[0]],[[-307482360,-33309135,-38745],[-33309135,-158130],[-38745]],[[0,0,0],[0,0],[0]],[[-594332805,-24832005,-6015],[-24832005,-24285],[-6015]],[[0,0,0],[0,0],[0]],[[-787875180,-12931470,-390],[-12931470,-1560],[-390]],[[0,0],[0]],[[-760736580,-4705650],[-4705650]],[[0,0],[0]],[[-550177080,-1173000],[-1173000]],[[0,0],[0]],[[-301737675,-190890],[-190890]],[[0,0],[0]],[[-125757765,-18270],[-18270]],[[0,0],[0]],[[-39559410,-780],[-780]],[[0]],[[-9233820]],[[0]],[[-1549695]],[[0]],[[-176715]],[[0]],[[-12255]],[[0]],[[-390]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
