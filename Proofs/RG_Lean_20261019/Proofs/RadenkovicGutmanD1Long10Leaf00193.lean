/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00193 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1007430896293101903962609549312000000000000 640670097965063513395092565676709478662144 2932776177583485613076694171648000000000000))
theorem leaf00193_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1007430896293101903962609549312000000000000 640670097965063513395092565676709478662144 2932776177583485613076694171648000000000000 raw00193=true := by decide +kernel
#print axioms leaf00193_raw
theorem leaf00193_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00193=true := by decide +kernel
#print axioms leaf00193_rectangular
def affine00193 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00193 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00193_transform : affine00193=(NestedInteger.clearedAll 3 raw00193 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00193_transform
theorem leaf00193_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00193=true := by decide +kernel
#print axioms leaf00193_sign
theorem leaf00193_log : RationalLog.accepts (2241665009/4294967296) (-349086921/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00193_log
def leaf00193 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (109225876639/500000000000) (2241665009/4294967296) (-349086921/1073741824) 1 8 ![52,0,4] ![(97/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00193
theorem leaf00193_checked : FastNestedCellData.accepts 1 0 4 leaf00193=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (109225876639/500000000000) (2241665009/4294967296) (-349086921/1073741824) 1 8 ![52,0,4] ![(97/3200),0,(1/4)] ![(3/3200),1,(1/4)] 1007430896293101903962609549312000000000000 640670097965063513395092565676709478662144 2932776177583485613076694171648000000000000 raw00193 affine00193
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00193_raw leaf00193_rectangular
    leaf00193_transform leaf00193_sign leaf00193_log
#print axioms leaf00193_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
