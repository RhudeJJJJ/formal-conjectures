/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00139 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 209591056194861241145982189568000000000000 203982788741728239407783739221805478445056 17953143457905241093784335286272000000000000))
theorem leaf00139_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 209591056194861241145982189568000000000000 203982788741728239407783739221805478445056 17953143457905241093784335286272000000000000 raw00139=true := by decide +kernel
#print axioms leaf00139_raw
theorem leaf00139_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00139=true := by decide +kernel
#print axioms leaf00139_rectangular
def affine00139 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00139 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(97/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00139_transform : affine00139=(NestedInteger.clearedAll 3 raw00139 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(97/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00139_transform
theorem leaf00139_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00139=true := by decide +kernel
#print axioms leaf00139_sign
theorem leaf00139_log : RationalLog.accepts (4133082059/4294967296) (-41253771/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00139_log
def leaf00139 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11361953923/1000000000000) (4133082059/4294967296) (-41253771/2147483648) 1 8 ![60,0,4] ![(97/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00139
theorem leaf00139_checked : FastNestedCellData.accepts 1 2 4 leaf00139=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11361953923/1000000000000) (4133082059/4294967296) (-41253771/2147483648) 1 8 ![60,0,4] ![(97/32000),0,(1/2)] ![(3/32000),1,(1/2)] 209591056194861241145982189568000000000000 203982788741728239407783739221805478445056 17953143457905241093784335286272000000000000 raw00139 affine00139
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00139_raw leaf00139_rectangular
    leaf00139_transform leaf00139_sign leaf00139_log
#print axioms leaf00139_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
