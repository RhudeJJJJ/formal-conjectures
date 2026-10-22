/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00417 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 30516230204696762889742267187200000000000 38774621386389486477438522748690646433792 937554229302707449138271118950400000000000))
theorem leaf00417_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 30516230204696762889742267187200000000000 38774621386389486477438522748690646433792 937554229302707449138271118950400000000000 raw00417=true := by decide +kernel
#print axioms leaf00417_raw
theorem leaf00417_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00417=true := by decide +kernel
#print axioms leaf00417_rectangular
def affine00417 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00417 (IntegerComputedClassCell.leftNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/2),0,0] ![(1/16),1,(1/2)]))
theorem leaf00417_transform : affine00417=(NestedInteger.clearedAll 3 raw00417 (IntegerComputedClassCell.leftNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/2),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf00417_transform
theorem leaf00417_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00417=true := by decide +kernel
#print axioms leaf00417_sign
theorem leaf00417_log : RationalLog.accepts (5240549397/4294967296) (427311447/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00417_log
def leaf00417 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (8271440771/200000000000) (5240549397/4294967296) (427311447/4294967296) 0 8 ![52,0,4] ![(1/2),0,0] ![(1/16),1,(1/2)] affine00417
theorem leaf00417_checked : FastNestedCellData.accepts 1 0 4 leaf00417=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (8271440771/200000000000) (5240549397/4294967296) (427311447/4294967296) 0 8 ![52,0,4] ![(1/2),0,0] ![(1/16),1,(1/2)] 30516230204696762889742267187200000000000 38774621386389486477438522748690646433792 937554229302707449138271118950400000000000 raw00417 affine00417
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00417_raw leaf00417_rectangular
    leaf00417_transform leaf00417_sign leaf00417_log
#print axioms leaf00417_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
