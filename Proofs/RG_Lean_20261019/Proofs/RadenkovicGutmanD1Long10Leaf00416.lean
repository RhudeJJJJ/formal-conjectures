/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00416 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 14985753450625212594371166208000000000000 19535492839349540474427888938387597426688 375738361634387691000387600384000000000000))
theorem leaf00416_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 14985753450625212594371166208000000000000 19535492839349540474427888938387597426688 375738361634387691000387600384000000000000 raw00416=true := by decide +kernel
#print axioms leaf00416_raw
theorem leaf00416_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00416=true := by decide +kernel
#print axioms leaf00416_rectangular
def affine00416 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00416 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]))
theorem leaf00416_transform : affine00416=(NestedInteger.clearedAll 3 raw00416 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00416_transform
theorem leaf00416_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00416=true := by decide +kernel
#print axioms leaf00416_sign
theorem leaf00416_log : RationalLog.accepts (5322223383/4294967296) (57565233/536870912) 0 8=true := by decide +kernel
#print axioms leaf00416_log
def leaf00416 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (6499034579/125000000000) (5322223383/4294967296) (57565233/536870912) 0 8 ![52,0,4] ![(9/16),0,(3/4)] ![(1/16),1,(1/4)] affine00416
theorem leaf00416_checked : FastNestedCellData.accepts 1 0 4 leaf00416=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (6499034579/125000000000) (5322223383/4294967296) (57565233/536870912) 0 8 ![52,0,4] ![(9/16),0,(3/4)] ![(1/16),1,(1/4)] 14985753450625212594371166208000000000000 19535492839349540474427888938387597426688 375738361634387691000387600384000000000000 raw00416 affine00416
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00416_raw leaf00416_rectangular
    leaf00416_transform leaf00416_sign leaf00416_log
#print axioms leaf00416_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
