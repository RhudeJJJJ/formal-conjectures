/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode071
import Proofs.RadenkovicGutmanD24Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-31104,0],[-31104,-6912,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-528768,-590976,0],[-590976,-81072,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10848816,-4762800,0],[-4762800,-386976,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-98577648,-21641760,0],[-21641760,-975024,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-528053184,-62065872,0],[-62065872,-1418208,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1872491376,-119184672,0],[-119184672,-1236288,0],[0,0]],[[0,0,0],[0,0],[0]],[[-4679292048,-158725392,0],[-158725392,-650208],[0]],[[0,0,0],[0,0],[0]],[[-8564637984,-149713344,0],[-149713344,-201264],[0]],[[0,0,0],[0,0],[0]],[[-11775429696,-101078880,0],[-101078880,-33696],[0]],[[0,0,0],[0,0],[0]],[[-12365935824,-48895296,0],[-48895296,-2352],[0]],[[0,0,0],[0,0],[0]],[[-10022572704,-16777104,0],[-16777104,0],[0]],[[0,0],[0]],[[-6302404128,-3980832],[-3980832]],[[0,0],[0]],[[-3075925248,-620496],[-620496]],[[0,0],[0]],[[-1159584528,-57120],[-57120]],[[0,0],[0]],[[-333929040,-2352],[-2352]],[[0,0],[0]],[[-72012960,0],[0]],[[0]],[[-11246976]],[[0]],[[-1200432]],[[0]],[[-78288]],[[0]],[[-2352]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
