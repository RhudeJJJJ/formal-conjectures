/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00489 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 215724154337208767874315845632000000000000 194007234230921252744527168762045878239232 4147428239203838543507283247104000000000000))
theorem leaf00489_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 215724154337208767874315845632000000000000 194007234230921252744527168762045878239232 4147428239203838543507283247104000000000000 raw00489=true := by decide +kernel
#print axioms leaf00489_raw
theorem leaf00489_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00489=true := by decide +kernel
#print axioms leaf00489_rectangular
def affine00489 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00489 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(81/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00489_transform : affine00489=(NestedInteger.clearedAll 3 raw00489 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(81/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00489_transform
theorem leaf00489_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00489=true := by decide +kernel
#print axioms leaf00489_sign
theorem leaf00489_log : RationalLog.accepts (3689984487/4294967296) (-163017313/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00489_log
def leaf00489 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (23388859679/500000000000) (3689984487/4294967296) (-163017313/2147483648) 1 8 ![60,0,4] ![(81/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00489
theorem leaf00489_checked : FastNestedCellData.accepts 1 2 4 leaf00489=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (23388859679/500000000000) (3689984487/4294967296) (-163017313/2147483648) 1 8 ![60,0,4] ![(81/6400),0,(1/2)] ![(1/6400),1,(1/2)] 215724154337208767874315845632000000000000 194007234230921252744527168762045878239232 4147428239203838543507283247104000000000000 raw00489 affine00489
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00489_raw leaf00489_rectangular
    leaf00489_transform leaf00489_sign leaf00489_log
#print axioms leaf00489_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
