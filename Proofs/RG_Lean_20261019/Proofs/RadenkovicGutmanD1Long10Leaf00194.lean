/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00194 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1966468607960205019307835392000000000000 1553022493654538214149808629161647931392 14226907046282463030735273984000000000000))
theorem leaf00194_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1966468607960205019307835392000000000000 1553022493654538214149808629161647931392 14226907046282463030735273984000000000000 raw00194=true := by decide +kernel
#print axioms leaf00194_raw
theorem leaf00194_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00194=true := by decide +kernel
#print axioms leaf00194_rectangular
def affine00194 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00194 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00194_transform : affine00194=(NestedInteger.clearedAll 3 raw00194 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00194_transform
theorem leaf00194_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00194=true := by decide +kernel
#print axioms leaf00194_sign
theorem leaf00194_log : RationalLog.accepts (3058130567/4294967296) (-729371677/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00194_log
def leaf00194 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (3411279259/31250000000) (3058130567/4294967296) (-729371677/4294967296) 1 8 ![52,0,4] ![(97/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00194
theorem leaf00194_checked : FastNestedCellData.accepts 1 0 4 leaf00194=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (3411279259/31250000000) (3058130567/4294967296) (-729371677/4294967296) 1 8 ![52,0,4] ![(97/3200),0,(1/2)] ![(3/3200),1,(1/2)] 1966468607960205019307835392000000000000 1553022493654538214149808629161647931392 14226907046282463030735273984000000000000 raw00194 affine00194
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00194_raw leaf00194_rectangular
    leaf00194_transform leaf00194_sign leaf00194_log
#print axioms leaf00194_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
