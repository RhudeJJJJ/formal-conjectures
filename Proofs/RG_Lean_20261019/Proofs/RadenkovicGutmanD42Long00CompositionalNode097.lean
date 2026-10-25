/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode051
import Proofs.RadenkovicGutmanD42Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5292],[0,-5292]],[[0,0,0],[0,0,0],[0,0]],[[0,47628,-79380],[47628,-238140,-23184],[-79380,-23184]],[[0,0,0],[0,0,0],[0,0]],[[714420,-1573992,-610848],[-1573992,-1754676,-29316],[-610848,-29316]],[[0,0,0],[0,0,0],[0,0]],[[-4082400,-19166868,-1871604],[-19166868,-5142564,-13692],[-1871604,-13692]],[[0,0,0],[0,0,0],[0,0]],[[-120469356,-89995500,-2995020],[-89995500,-7918260,-2352],[-2995020,-2352]],[[0,0,0],[0,0,0],[0,0]],[[-837995004,-236689572,-2751924],[-236689572,-7053144,-84],[-2751924,-84]],[[0,0,0],[0,0],[0]],[[-3173494464,-395728452,-1498140],[-395728452,-3750264],[-1498140]],[[0,0,0],[0,0],[0]],[[-7808379684,-446453700,-478380],[-446453700,-1178100],[-478380]],[[0,0,0],[0,0],[0]],[[-13491112152,-350092764,-83748],[-350092764,-204708],[-83748]],[[0,0,0],[0,0],[0]],[[-17071471116,-193013184,-6552],[-193013184,-16212],[-6552]],[[0,0,0],[0,0],[0]],[[-16211577228,-74565540,-84],[-74565540,-252],[-84]],[[0,0],[0]],[[-11711833056,-19788720],[-19788720]],[[0,0],[0]],[[-6474120912,-3450888],[-3450888]],[[0,0],[0]],[[-2735530308,-360696],[-360696]],[[0,0],[0]],[[-876297240,-18144],[-18144]],[[0,0],[0]],[[-209209140,-168],[-168]],[[0]],[[-36119160]],[[0]],[[-4279380]],[[0]],[[-315504]],[[0]],[[-11592]],[[0]],[[-84]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
