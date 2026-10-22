/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01266 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 56468845510285626988648464384000000000000 59839308502427313671633703471762534039552 19547777177257280532346933608448000000000000))
theorem leaf01266_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 56468845510285626988648464384000000000000 59839308502427313671633703471762534039552 19547777177257280532346933608448000000000000 raw01266=true := by decide +kernel
#print axioms leaf01266_raw
theorem leaf01266_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01266=true := by decide +kernel
#print axioms leaf01266_rectangular
def affine01266 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01266 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01266_transform : affine01266=(NestedInteger.clearedAll 3 raw01266 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01266_transform
theorem leaf01266_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01266=true := by decide +kernel
#print axioms leaf01266_sign
theorem leaf01266_log : RationalLog.accepts (4537431637/4294967296) (29483443/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01266_log
def leaf01266 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3061182249/1000000000000) (4537431637/4294967296) (29483443/1073741824) 0 8 ![60,0,4] ![(3/16),0,(1/2)] ![(1/128),1,(1/4)] affine01266
theorem leaf01266_checked : FastNestedCellData.accepts 1 2 4 leaf01266=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3061182249/1000000000000) (4537431637/4294967296) (29483443/1073741824) 0 8 ![60,0,4] ![(3/16),0,(1/2)] ![(1/128),1,(1/4)] 56468845510285626988648464384000000000000 59839308502427313671633703471762534039552 19547777177257280532346933608448000000000000 raw01266 affine01266
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01266_raw leaf01266_rectangular
    leaf01266_transform leaf01266_sign leaf01266_log
#print axioms leaf01266_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
