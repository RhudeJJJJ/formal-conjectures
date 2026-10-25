/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode051
import Proofs.RadenkovicGutmanD38Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4332],[0,-4332]],[[0,0,0],[0,0,0],[0,0]],[[0,38988,-64980],[38988,-194940,-19000],[-64980,-19000]],[[0,0,0],[0,0,0],[0,0]],[[584820,-1288656,-500232],[-1288656,-1437084,-24092],[-500232,-24092]],[[0,0,0],[0,0,0],[0,0]],[[-3344760,-15697116,-1533452],[-15697116,-4214580,-11324],[-1533452,-11324]],[[0,0,0],[0,0,0],[0,0]],[[-98686836,-73728284,-2455484],[-73728284,-6495036,-1976],[-2455484,-1976]],[[0,0,0],[0,0,0],[0,0]],[[-686600796,-193978220,-2258188],[-193978220,-5792264,-76],[-2258188,-76]],[[0,0,0],[0,0],[0]],[[-2600748424,-324454564,-1230972],[-324454564,-3085144],[-1230972]],[[0,0,0],[0,0],[0]],[[-6400733452,-366224924,-393908],[-366224924,-971812],[-393908]],[[0,0,0],[0,0],[0]],[[-11062053384,-287353644,-69236],[-287353644,-169708],[-69236]],[[0,0,0],[0,0],[0]],[[-14002059500,-158545576,-5472],[-158545576,-13604],[-5472]],[[0,0,0],[0,0],[0]],[[-13301408660,-61312924,-76],[-61312924,-228],[-76]],[[0,0],[0]],[[-9613329984,-16295616],[-16295616]],[[0,0],[0]],[[-5316693392,-2848328],[-2848328]],[[0,0],[0]],[[-2247836420,-298984],[-298984]],[[0,0],[0]],[[-720629872,-15200],[-15200]],[[0,0],[0]],[[-172225500,-152],[-152]],[[0]],[[-29779080]],[[0]],[[-3536660]],[[0]],[[-261896]],[[0]],[[-9728]],[[0]],[[-76]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
