/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00558 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 194862937482100137158481281024000000000000 147691844056689363460915792378368180092928 1165106819991629931050063364096000000000000))
theorem leaf00558_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 194862937482100137158481281024000000000000 147691844056689363460915792378368180092928 1165106819991629931050063364096000000000000 raw00558=true := by decide +kernel
#print axioms leaf00558_raw
theorem leaf00558_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00558=true := by decide +kernel
#print axioms leaf00558_rectangular
def affine00558 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00558 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00558_transform : affine00558=(NestedInteger.clearedAll 3 raw00558 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00558_transform
theorem leaf00558_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00558=true := by decide +kernel
#print axioms leaf00558_sign
theorem leaf00558_log : RationalLog.accepts (1444523967/2147483648) (-425756827/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00558_log
def leaf00558 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (126762492093/1000000000000) (1444523967/2147483648) (-425756827/2147483648) 1 8 ![60,0,4] ![(27/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00558
theorem leaf00558_checked : FastNestedCellData.accepts 1 2 4 leaf00558=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (126762492093/1000000000000) (1444523967/2147483648) (-425756827/2147483648) 1 8 ![60,0,4] ![(27/1600),0,(1/4)] ![(1/3200),1,(1/4)] 194862937482100137158481281024000000000000 147691844056689363460915792378368180092928 1165106819991629931050063364096000000000000 raw00558 affine00558
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00558_raw leaf00558_rectangular
    leaf00558_transform leaf00558_sign leaf00558_log
#print axioms leaf00558_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
