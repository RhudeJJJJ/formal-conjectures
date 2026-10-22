/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00038 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 66500874488643773045669888000000000000 64036955853201707185115616962836168704 4336737114151319651292807168000000000000))
theorem leaf00038_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 66500874488643773045669888000000000000 64036955853201707185115616962836168704 4336737114151319651292807168000000000000 raw00038=true := by decide +kernel
#print axioms leaf00038_raw
theorem leaf00038_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00038=true := by decide +kernel
#print axioms leaf00038_rectangular
def affine00038 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00038 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/2)] ![(3/8000),1,(1/2)]))
theorem leaf00038_transform : affine00038=(NestedInteger.clearedAll 3 raw00038 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/2)] ![(3/8000),1,(1/2)])) := by decide +kernel
#print axioms leaf00038_transform
theorem leaf00038_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00038=true := by decide +kernel
#print axioms leaf00038_sign
theorem leaf00038_log : RationalLog.accepts (63682079/67108864) (-112555985/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00038_log
def leaf00038 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (14766160403/1000000000000) (63682079/67108864) (-112555985/4294967296) 1 8 ![52,0,4] ![(31/8000),0,(1/2)] ![(3/8000),1,(1/2)] affine00038
theorem leaf00038_checked : FastNestedCellData.accepts 1 0 4 leaf00038=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (14766160403/1000000000000) (63682079/67108864) (-112555985/4294967296) 1 8 ![52,0,4] ![(31/8000),0,(1/2)] ![(3/8000),1,(1/2)] 66500874488643773045669888000000000000 64036955853201707185115616962836168704 4336737114151319651292807168000000000000 raw00038 affine00038
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00038_raw leaf00038_rectangular
    leaf00038_transform leaf00038_sign leaf00038_log
#print axioms leaf00038_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
