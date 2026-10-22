/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00802 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 22444007583212381538609843404800000000000 8937789502188527917351266859201857585152 18364937157533431562816297369600000000000))
theorem leaf00802_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 22444007583212381538609843404800000000000 8937789502188527917351266859201857585152 18364937157533431562816297369600000000000 raw00802=true := by decide +kernel
#print axioms leaf00802_raw
theorem leaf00802_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00802=true := by decide +kernel
#print axioms leaf00802_rectangular
def affine00802 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00802 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00802_transform : affine00802=(NestedInteger.clearedAll 3 raw00802 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00802_transform
theorem leaf00802_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00802=true := by decide +kernel
#print axioms leaf00802_sign
theorem leaf00802_log : RationalLog.accepts (1150463917/4294967296) (-2828834483/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00802_log
def leaf00802 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (24333841781/50000000000) (1150463917/4294967296) (-2828834483/4294967296) 2 8 ![60,0,4] ![(17/400),0,(1/8)] ![(3/3200),1,(1/8)] affine00802
theorem leaf00802_checked : FastNestedCellData.accepts 1 2 4 leaf00802=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (24333841781/50000000000) (1150463917/4294967296) (-2828834483/4294967296) 2 8 ![60,0,4] ![(17/400),0,(1/8)] ![(3/3200),1,(1/8)] 22444007583212381538609843404800000000000 8937789502188527917351266859201857585152 18364937157533431562816297369600000000000 raw00802 affine00802
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00802_raw leaf00802_rectangular
    leaf00802_transform leaf00802_sign leaf00802_log
#print axioms leaf00802_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
