/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00IntegerNorm
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00IntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def raw : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree03Long00IntegerNorm.pack true 554452277498467617856431795553719887942438092800000000000 554455449524071857599710726616203862780889303008805912576 278760909765747540271347776076522806827998644046659584000000000000))
noncomputable def affine : NestedInteger.Poly 3 := rg_closed_integer_data% (NestedInteger.clearedAll 3 raw (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/4096),(1/2),(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/4096),(1/2),(1/2)]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/4096),(1/2),(1/2)]))
#print axioms raw
#print axioms affine
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00IntegerLeaf03800
