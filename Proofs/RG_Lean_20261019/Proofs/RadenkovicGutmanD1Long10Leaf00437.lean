/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00437 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 45709303276820288765952000000000000 51359403708670532627690493692608512 4941686486126056097972224000000000000))
theorem leaf00437_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 45709303276820288765952000000000000 51359403708670532627690493692608512 4941686486126056097972224000000000000 raw00437=true := by decide +kernel
#print axioms leaf00437_raw
theorem leaf00437_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00437=true := by decide +kernel
#print axioms leaf00437_rectangular
def affine00437 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00437 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/32),0,(3/4)] ![(1/32),1,(1/4)]))
theorem leaf00437_transform : affine00437=(NestedInteger.clearedAll 3 raw00437 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/32),0,(3/4)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00437_transform
theorem leaf00437_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00437=true := by decide +kernel
#print axioms leaf00437_sign
theorem leaf00437_log : RationalLog.accepts (149257061/134217728) (228077245/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00437_log
def leaf00437 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (162392067/15625000000) (149257061/134217728) (228077245/4294967296) 0 8 ![52,0,4] ![(9/32),0,(3/4)] ![(1/32),1,(1/4)] affine00437
theorem leaf00437_checked : FastNestedCellData.accepts 1 0 4 leaf00437=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (162392067/15625000000) (149257061/134217728) (228077245/4294967296) 0 8 ![52,0,4] ![(9/32),0,(3/4)] ![(1/32),1,(1/4)] 45709303276820288765952000000000000 51359403708670532627690493692608512 4941686486126056097972224000000000000 raw00437 affine00437
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00437_raw leaf00437_rectangular
    leaf00437_transform leaf00437_sign leaf00437_log
#print axioms leaf00437_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
