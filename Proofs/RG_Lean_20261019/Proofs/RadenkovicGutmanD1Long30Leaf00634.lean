/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00634 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 302662226565855050690406750617600000000000 252705856895925324134790260349003741790208 3080397789297506365343013011456000000000000))
theorem leaf00634_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 302662226565855050690406750617600000000000 252705856895925324134790260349003741790208 3080397789297506365343013011456000000000000 raw00634=true := by decide +kernel
#print axioms leaf00634_raw
theorem leaf00634_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00634=true := by decide +kernel
#print axioms leaf00634_rectangular
def affine00634 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00634 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00634_transform : affine00634=(NestedInteger.clearedAll 3 raw00634 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00634_transform
theorem leaf00634_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00634=true := by decide +kernel
#print axioms leaf00634_sign
theorem leaf00634_log : RationalLog.accepts (3314171135/4294967296) (-278352965/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00634_log
def leaf00634 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (82036760893/1000000000000) (3314171135/4294967296) (-278352965/2147483648) 1 8 ![60,0,4] ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00634
theorem leaf00634_checked : FastNestedCellData.accepts 1 2 4 leaf00634=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (82036760893/1000000000000) (3314171135/4294967296) (-278352965/2147483648) 1 8 ![60,0,4] ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)] 302662226565855050690406750617600000000000 252705856895925324134790260349003741790208 3080397789297506365343013011456000000000000 raw00634 affine00634
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00634_raw leaf00634_rectangular
    leaf00634_transform leaf00634_sign leaf00634_log
#print axioms leaf00634_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
