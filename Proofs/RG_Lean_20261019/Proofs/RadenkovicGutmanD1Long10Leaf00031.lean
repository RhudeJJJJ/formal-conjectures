/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00031 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1807572070951741041858838528000000000000 1695436094908953537814080857337940148224 67587371926959214919824703488000000000000))
theorem leaf00031_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1807572070951741041858838528000000000000 1695436094908953537814080857337940148224 67587371926959214919824703488000000000000 raw00031=true := by decide +kernel
#print axioms leaf00031_raw
theorem leaf00031_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00031=true := by decide +kernel
#print axioms leaf00031_rectangular
def affine00031 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00031 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/4)] ![(3/8000),1,(1/4)]))
theorem leaf00031_transform : affine00031=(NestedInteger.clearedAll 3 raw00031 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/4)] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00031_transform
theorem leaf00031_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00031=true := by decide +kernel
#print axioms leaf00031_sign
theorem leaf00031_log : RationalLog.accepts (3929938391/4294967296) (-190739945/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00031_log
def leaf00031 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1567818853/62500000000) (3929938391/4294967296) (-190739945/4294967296) 1 8 ![52,0,4] ![(1/320),0,(1/4)] ![(3/8000),1,(1/4)] affine00031
theorem leaf00031_checked : FastNestedCellData.accepts 1 0 4 leaf00031=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1567818853/62500000000) (3929938391/4294967296) (-190739945/4294967296) 1 8 ![52,0,4] ![(1/320),0,(1/4)] ![(3/8000),1,(1/4)] 1807572070951741041858838528000000000000 1695436094908953537814080857337940148224 67587371926959214919824703488000000000000 raw00031 affine00031
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00031_raw leaf00031_rectangular
    leaf00031_transform leaf00031_sign leaf00031_log
#print axioms leaf00031_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
