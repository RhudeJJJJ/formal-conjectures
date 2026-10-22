/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00737 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7610213560027075441851459698688000000000000 3353394903340696678440321835958412811173888 8128446997194087918795034198016000000000000))
theorem leaf00737_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7610213560027075441851459698688000000000000 3353394903340696678440321835958412811173888 8128446997194087918795034198016000000000000 raw00737=true := by decide +kernel
#print axioms leaf00737_raw
theorem leaf00737_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00737=true := by decide +kernel
#print axioms leaf00737_rectangular
def affine00737 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00737 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00737_transform : affine00737=(NestedInteger.clearedAll 3 raw00737 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00737_transform
theorem leaf00737_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00737=true := by decide +kernel
#print axioms leaf00737_sign
theorem leaf00737_log : RationalLog.accepts (1339811597/4294967296) (-312704481/536870912) 2 8=true := by decide +kernel
#print axioms leaf00737_log
def leaf00737 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (412550503743/1000000000000) (1339811597/4294967296) (-312704481/536870912) 2 8 ![60,0,4] ![(103/3200),0,(1/8)] ![(3/6400),1,(1/8)] affine00737
theorem leaf00737_checked : FastNestedCellData.accepts 1 2 4 leaf00737=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (412550503743/1000000000000) (1339811597/4294967296) (-312704481/536870912) 2 8 ![60,0,4] ![(103/3200),0,(1/8)] ![(3/6400),1,(1/8)] 7610213560027075441851459698688000000000000 3353394903340696678440321835958412811173888 8128446997194087918795034198016000000000000 raw00737 affine00737
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00737_raw leaf00737_rectangular
    leaf00737_transform leaf00737_sign leaf00737_log
#print axioms leaf00737_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
