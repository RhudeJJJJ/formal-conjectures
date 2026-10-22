/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00430 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 25910815711241891962786152448000000000000 30250462011892505156901380846316391759872 1794689834879601643392600113152000000000000))
theorem leaf00430_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 25910815711241891962786152448000000000000 30250462011892505156901380846316391759872 1794689834879601643392600113152000000000000 raw00430=true := by decide +kernel
#print axioms leaf00430_raw
theorem leaf00430_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00430=true := by decide +kernel
#print axioms leaf00430_rectangular
def affine00430 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00430 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/32),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf00430_transform : affine00430=(NestedInteger.clearedAll 3 raw00430 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/32),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00430_transform
theorem leaf00430_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00430=true := by decide +kernel
#print axioms leaf00430_sign
theorem leaf00430_log : RationalLog.accepts (2465593827/2147483648) (37080579/536870912) 0 8=true := by decide +kernel
#print axioms leaf00430_log
def leaf00430 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (16855537611/1000000000000) (2465593827/2147483648) (37080579/536870912) 0 8 ![52,0,4] ![(11/32),0,(1/2)] ![(1/32),1,(1/4)] affine00430
theorem leaf00430_checked : FastNestedCellData.accepts 1 0 4 leaf00430=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (16855537611/1000000000000) (2465593827/2147483648) (37080579/536870912) 0 8 ![52,0,4] ![(11/32),0,(1/2)] ![(1/32),1,(1/4)] 25910815711241891962786152448000000000000 30250462011892505156901380846316391759872 1794689834879601643392600113152000000000000 raw00430 affine00430
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00430_raw leaf00430_rectangular
    leaf00430_transform leaf00430_sign leaf00430_log
#print axioms leaf00430_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
