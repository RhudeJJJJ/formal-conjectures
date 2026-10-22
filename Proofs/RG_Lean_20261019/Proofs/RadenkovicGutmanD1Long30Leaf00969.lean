/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00969 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 68425238010894930717492799078400000000000 45370045070450546235411398389146702577664 152891249332229159455494766592000000000000))
theorem leaf00969_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 68425238010894930717492799078400000000000 45370045070450546235411398389146702577664 152891249332229159455494766592000000000000 raw00969=true := by decide +kernel
#print axioms leaf00969_raw
theorem leaf00969_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00969=true := by decide +kernel
#print axioms leaf00969_rectangular
def affine00969 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00969 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00969_transform : affine00969=(NestedInteger.clearedAll 3 raw00969 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00969_transform
theorem leaf00969_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00969=true := by decide +kernel
#print axioms leaf00969_sign
theorem leaf00969_log : RationalLog.accepts (549031745/1073741824) (-1440421677/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00969_log
def leaf00969 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (296747166817/1000000000000) (549031745/1073741824) (-1440421677/4294967296) 1 8 ![60,0,4] ![(17/160),0,(1/2)] ![(1/160),1,(1/2)] affine00969
theorem leaf00969_checked : FastNestedCellData.accepts 1 2 4 leaf00969=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (296747166817/1000000000000) (549031745/1073741824) (-1440421677/4294967296) 1 8 ![60,0,4] ![(17/160),0,(1/2)] ![(1/160),1,(1/2)] 68425238010894930717492799078400000000000 45370045070450546235411398389146702577664 152891249332229159455494766592000000000000 raw00969 affine00969
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00969_raw leaf00969_rectangular
    leaf00969_transform leaf00969_sign leaf00969_log
#print axioms leaf00969_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
