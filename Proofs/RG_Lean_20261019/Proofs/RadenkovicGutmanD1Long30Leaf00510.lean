/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00510 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2831173630806425509354634687283200000000000 19618080809517357708319061353536602243072 25564643013960221148129001472000000000000))
theorem leaf00510_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2831173630806425509354634687283200000000000 19618080809517357708319061353536602243072 25564643013960221148129001472000000000000 raw00510=true := by decide +kernel
#print axioms leaf00510_raw
theorem leaf00510_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00510=true := by decide +kernel
#print axioms leaf00510_rectangular
def affine00510 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00510 (IntegerComputedClassCell.leftNumerator ![(9/640),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/640),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00510_transform : affine00510=(NestedInteger.clearedAll 3 raw00510 (IntegerComputedClassCell.leftNumerator ![(9/640),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/640),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00510_transform
theorem leaf00510_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00510=true := by decide +kernel
#print axioms leaf00510_sign
theorem leaf00510_log : RationalLog.accepts (16839035/4294967296) (-1487534985/536870912) 8 8=true := by decide +kernel
#print axioms leaf00510_log
def leaf00510 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (767391150301/1000000000000) (16839035/4294967296) (-1487534985/536870912) 8 8 ![60,0,4] ![(9/640),0,0] ![(1/3200),1,(1/16)] affine00510
theorem leaf00510_checked : FastNestedCellData.accepts 1 2 4 leaf00510=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (767391150301/1000000000000) (16839035/4294967296) (-1487534985/536870912) 8 8 ![60,0,4] ![(9/640),0,0] ![(1/3200),1,(1/16)] 2831173630806425509354634687283200000000000 19618080809517357708319061353536602243072 25564643013960221148129001472000000000000 raw00510 affine00510
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00510_raw leaf00510_rectangular
    leaf00510_transform leaf00510_sign leaf00510_log
#print axioms leaf00510_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
