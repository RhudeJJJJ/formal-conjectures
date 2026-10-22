/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00519 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1228914237065701699119742976000000000 1088749171424293771291456208524804096 20428477350138233537607761920000000000))
theorem leaf00519_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1228914237065701699119742976000000000 1088749171424293771291456208524804096 20428477350138233537607761920000000000 raw00519=true := by decide +kernel
#print axioms leaf00519_raw
theorem leaf00519_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00519=true := by decide +kernel
#print axioms leaf00519_rectangular
def affine00519 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00519 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00519_transform : affine00519=(NestedInteger.clearedAll 3 raw00519 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00519_transform
theorem leaf00519_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00519=true := by decide +kernel
#print axioms leaf00519_sign
theorem leaf00519_log : RationalLog.accepts (225785395/268435456) (-185784765/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00519_log
def leaf00519 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2131826377/40000000000) (225785395/268435456) (-185784765/2147483648) 1 8 ![60,0,4] ![(23/1600),0,(1/2)] ![(1/3200),1,(1/2)] affine00519
theorem leaf00519_checked : FastNestedCellData.accepts 1 2 4 leaf00519=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2131826377/40000000000) (225785395/268435456) (-185784765/2147483648) 1 8 ![60,0,4] ![(23/1600),0,(1/2)] ![(1/3200),1,(1/2)] 1228914237065701699119742976000000000 1088749171424293771291456208524804096 20428477350138233537607761920000000000 raw00519 affine00519
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00519_raw leaf00519_rectangular
    leaf00519_transform leaf00519_sign leaf00519_log
#print axioms leaf00519_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
