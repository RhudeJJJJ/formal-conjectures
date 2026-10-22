/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00402 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 10176332566814250411663294464000000000000 13949781551030461597033062908668982329344 98777009234143821007008301056000000000000))
theorem leaf00402_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 10176332566814250411663294464000000000000 13949781551030461597033062908668982329344 98777009234143821007008301056000000000000 raw00402=true := by decide +kernel
#print axioms leaf00402_raw
theorem leaf00402_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00402=true := by decide +kernel
#print axioms leaf00402_rectangular
def affine00402 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00402 (IntegerComputedClassCell.leftNumerator ![(7/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/8),0,0] ![(1/8),1,(1/2)]))
theorem leaf00402_transform : affine00402=(NestedInteger.clearedAll 3 raw00402 (IntegerComputedClassCell.leftNumerator ![(7/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/8),0,0] ![(1/8),1,(1/2)])) := by decide +kernel
#print axioms leaf00402_transform
theorem leaf00402_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00402=true := by decide +kernel
#print axioms leaf00402_sign
theorem leaf00402_log : RationalLog.accepts (2579495117/2147483648) (98406789/1073741824) 0 8=true := by decide +kernel
#print axioms leaf00402_log
def leaf00402 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (17653123003/125000000000) (2579495117/2147483648) (98406789/1073741824) 0 8 ![52,0,4] ![(7/8),0,0] ![(1/8),1,(1/2)] affine00402
theorem leaf00402_checked : FastNestedCellData.accepts 1 0 4 leaf00402=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (17653123003/125000000000) (2579495117/2147483648) (98406789/1073741824) 0 8 ![52,0,4] ![(7/8),0,0] ![(1/8),1,(1/2)] 10176332566814250411663294464000000000000 13949781551030461597033062908668982329344 98777009234143821007008301056000000000000 raw00402 affine00402
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00402_raw leaf00402_rectangular
    leaf00402_transform leaf00402_sign leaf00402_log
#print axioms leaf00402_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
