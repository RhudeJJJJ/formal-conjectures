/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00360 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 135283399792266150849633111244800000000000 95562487677390147493626552977322028302336 173740631980836724938104215961600000000000))
theorem leaf00360_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 135283399792266150849633111244800000000000 95562487677390147493626552977322028302336 173740631980836724938104215961600000000000 raw00360=true := by decide +kernel
#print axioms leaf00360_raw
theorem leaf00360_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00360=true := by decide +kernel
#print axioms leaf00360_rectangular
def affine00360 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00360 (IntegerComputedClassCell.leftNumerator ![(7/32),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,0] ![(3/160),1,(1/4)]))
theorem leaf00360_transform : affine00360=(NestedInteger.clearedAll 3 raw00360 (IntegerComputedClassCell.leftNumerator ![(7/32),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,0] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00360_transform
theorem leaf00360_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00360=true := by decide +kernel
#print axioms leaf00360_sign
theorem leaf00360_log : RationalLog.accepts (1957324407/4294967296) (-1687633379/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00360_log
def leaf00360 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (110005916967/200000000000) (1957324407/4294967296) (-1687633379/4294967296) 2 8 ![52,0,4] ![(7/32),0,0] ![(3/160),1,(1/4)] affine00360
theorem leaf00360_checked : FastNestedCellData.accepts 1 0 4 leaf00360=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (110005916967/200000000000) (1957324407/4294967296) (-1687633379/4294967296) 2 8 ![52,0,4] ![(7/32),0,0] ![(3/160),1,(1/4)] 135283399792266150849633111244800000000000 95562487677390147493626552977322028302336 173740631980836724938104215961600000000000 raw00360 affine00360
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00360_raw leaf00360_rectangular
    leaf00360_transform leaf00360_sign leaf00360_log
#print axioms leaf00360_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
