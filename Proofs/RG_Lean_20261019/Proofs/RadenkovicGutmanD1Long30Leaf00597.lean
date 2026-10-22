/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00597 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 201913807438542422696106393600000000000 111786615912809407900630790827942084608 398936293188902454611987660800000000000))
theorem leaf00597_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 201913807438542422696106393600000000000 111786615912809407900630790827942084608 398936293188902454611987660800000000000 raw00597=true := by decide +kernel
#print axioms leaf00597_raw
theorem leaf00597_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00597=true := by decide +kernel
#print axioms leaf00597_rectangular
def affine00597 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00597 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00597_transform : affine00597=(NestedInteger.clearedAll 3 raw00597 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00597_transform
theorem leaf00597_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00597=true := by decide +kernel
#print axioms leaf00597_sign
theorem leaf00597_log : RationalLog.accepts (116086543/268435456) (-1800180905/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00597_log
def leaf00597 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (28021169751/100000000000) (116086543/268435456) (-1800180905/4294967296) 2 8 ![60,0,4] ![(31/1600),0,(1/8)] ![(1/3200),1,(1/8)] affine00597
theorem leaf00597_checked : FastNestedCellData.accepts 1 2 4 leaf00597=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (28021169751/100000000000) (116086543/268435456) (-1800180905/4294967296) 2 8 ![60,0,4] ![(31/1600),0,(1/8)] ![(1/3200),1,(1/8)] 201913807438542422696106393600000000000 111786615912809407900630790827942084608 398936293188902454611987660800000000000 raw00597 affine00597
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00597_raw leaf00597_rectangular
    leaf00597_transform leaf00597_sign leaf00597_log
#print axioms leaf00597_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
