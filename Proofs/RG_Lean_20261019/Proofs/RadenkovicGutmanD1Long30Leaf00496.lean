/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00496 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3448503387176147729425744527360000000000 1525645299386527262789988778176468221952 4080493075589912017120106905600000000000))
theorem leaf00496_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3448503387176147729425744527360000000000 1525645299386527262789988778176468221952 4080493075589912017120106905600000000000 raw00496=true := by decide +kernel
#print axioms leaf00496_raw
theorem leaf00496_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00496=true := by decide +kernel
#print axioms leaf00496_rectangular
def affine00496 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00496 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00496_transform : affine00496=(NestedInteger.clearedAll 3 raw00496 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00496_transform
theorem leaf00496_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00496=true := by decide +kernel
#print axioms leaf00496_sign
theorem leaf00496_log : RationalLog.accepts (1383030035/4294967296) (-1216729021/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00496_log
def leaf00496 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18694374321/50000000000) (1383030035/4294967296) (-1216729021/2147483648) 2 8 ![60,0,4] ![(21/1600),0,(1/16)] ![(1/3200),1,(1/16)] affine00496
theorem leaf00496_checked : FastNestedCellData.accepts 1 2 4 leaf00496=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18694374321/50000000000) (1383030035/4294967296) (-1216729021/2147483648) 2 8 ![60,0,4] ![(21/1600),0,(1/16)] ![(1/3200),1,(1/16)] 3448503387176147729425744527360000000000 1525645299386527262789988778176468221952 4080493075589912017120106905600000000000 raw00496 affine00496
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00496_raw leaf00496_rectangular
    leaf00496_transform leaf00496_sign leaf00496_log
#print axioms leaf00496_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
