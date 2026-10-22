/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerAffineStages
import Proofs.RadenkovicGutmanD1IntegerNorm00
namespace Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00000 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack false 181408637241908976965048598528000000000000 7007103772058997510159012847058681856 11133208355793004698533888000000000000))
theorem leaf00000_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack
    false 181408637241908976965048598528000000000000 7007103772058997510159012847058681856 11133208355793004698533888000000000000 raw00000=true := by decide +kernel
#print axioms leaf00000_raw
theorem leaf00000_rectangular : NestedInteger.rectangular 3 ![88,4,4] raw00000=true := by decide +kernel
#print axioms leaf00000_rectangular
end Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
