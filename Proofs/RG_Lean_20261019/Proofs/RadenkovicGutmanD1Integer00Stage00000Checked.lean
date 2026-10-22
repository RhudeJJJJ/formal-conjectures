/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Integer00Stage00000Affine
namespace Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine00000=true := by decide +kernel
#print axioms leaf00000_sign
theorem leaf00000_log : RationalLog.accepts (12727/536870912) (-22870244509/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00000_log
def leaf00000 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)] affine00000
theorem leaf00000_checked : FastNestedCellData.accepts 1 4 4 leaf00000=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)] 181408637241908976965048598528000000000000 7007103772058997510159012847058681856 11133208355793004698533888000000000000 raw00000 affine00000
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00000_raw leaf00000_rectangular
    leaf00000_transform leaf00000_sign leaf00000_log
#print axioms leaf00000_checked
end Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
