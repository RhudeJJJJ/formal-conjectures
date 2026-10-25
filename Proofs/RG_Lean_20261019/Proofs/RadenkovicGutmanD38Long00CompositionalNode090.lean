/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode035
import Proofs.RadenkovicGutmanD38Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4332],[0,-4332]],[[0,0,0],[0,0,0],[0,0]],[[0,-38988,-64980],[-38988,-207936,-19000],[-64980,-19000]],[[0,0,0],[0,0,0],[0,0]],[[-701784,-2419308,-500232],[-2419308,-1550400,-24092],[-500232,-24092]],[[0,0,0],[0,0,0],[0,0]],[[-24365448,-22669128,-1533452],[-22669128,-4603168,-11324],[-1533452,-11324]],[[0,0,0],[0,0,0],[0,0]],[[-251525952,-97934512,-2455484],[-97934512,-7176528,-1976],[-2455484,-1976]],[[0,0,0],[0,0,0],[0,0]],[[-1344131136,-246924608,-2258188],[-246924608,-6468208,-76],[-2258188,-76]],[[0,0,0],[0,0],[0]],[[-4479540168,-401943632,-1230972],[-401943632,-3479888],[-1230972]],[[0,0,0],[0,0],[0]],[[-10195836392,-444843504,-393908],[-444843504,-1107776],[-393908]],[[0,0,0],[0,0],[0]],[[-16692185216,-343775436,-69236],[-343775436,-196080],[-69236]],[[0,0,0],[0,0],[0]],[[-20288728200,-187432872,-5472],[-187432872,-16112],[-5472]],[[0,0,0],[0,0],[0]],[[-18668629664,-71837480,-76],[-71837480,-304],[-76]],[[0,0],[0]],[[-13149243664,-18982292],[-18982292]],[[0,0],[0]],[[-7121015928,-3312916],[-3312916]],[[0,0],[0]],[[-2959982032,-349980],[-349980]],[[0,0],[0]],[[-936493736,-18316],[-18316]],[[0,0],[0]],[[-221770280,-228],[-228]],[[0]],[[-38185136]],[[0]],[[-4550120]],[[0]],[[-343064]],[[0]],[[-13528]],[[0]],[[-152]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
