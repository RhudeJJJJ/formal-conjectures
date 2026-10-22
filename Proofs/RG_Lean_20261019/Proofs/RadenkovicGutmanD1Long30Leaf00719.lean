/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00719 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 20208243020000893717347586539520000000000 16028336685199744031502196946478261338112 146311890878634485603836624896000000000000))
theorem leaf00719_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 20208243020000893717347586539520000000000 16028336685199744031502196946478261338112 146311890878634485603836624896000000000000 raw00719=true := by decide +kernel
#print axioms leaf00719_raw
theorem leaf00719_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00719=true := by decide +kernel
#print axioms leaf00719_rectangular
def affine00719 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00719 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00719_transform : affine00719=(NestedInteger.clearedAll 3 raw00719 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00719_transform
theorem leaf00719_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00719=true := by decide +kernel
#print axioms leaf00719_sign
theorem leaf00719_log : RationalLog.accepts (3070246425/4294967296) (-180220119/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00719_log
def leaf00719 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (54774552461/500000000000) (3070246425/4294967296) (-180220119/1073741824) 1 8 ![60,0,4] ![(97/3200),0,(1/2)] ![(3/6400),1,(1/2)] affine00719
theorem leaf00719_checked : FastNestedCellData.accepts 1 2 4 leaf00719=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (54774552461/500000000000) (3070246425/4294967296) (-180220119/1073741824) 1 8 ![60,0,4] ![(97/3200),0,(1/2)] ![(3/6400),1,(1/2)] 20208243020000893717347586539520000000000 16028336685199744031502196946478261338112 146311890878634485603836624896000000000000 raw00719 affine00719
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00719_raw leaf00719_rectangular
    leaf00719_transform leaf00719_sign leaf00719_log
#print axioms leaf00719_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
