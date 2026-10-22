/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00540 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 45835895932593620821506365849600000000000 415689757361669908651221230643784450048 522797308480529198579974144000000000000))
theorem leaf00540_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 45835895932593620821506365849600000000000 415689757361669908651221230643784450048 522797308480529198579974144000000000000 raw00540=true := by decide +kernel
#print axioms leaf00540_raw
theorem leaf00540_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00540=true := by decide +kernel
#print axioms leaf00540_rectangular
def affine00540 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00540 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(51/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00540_transform : affine00540=(NestedInteger.clearedAll 3 raw00540 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(51/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00540_transform
theorem leaf00540_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00540=true := by decide +kernel
#print axioms leaf00540_sign
theorem leaf00540_log : RationalLog.accepts (2712305/536870912) (-11355805447/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00540_log
def leaf00540 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (795126047167/1000000000000) (2712305/536870912) (-11355805447/4294967296) 8 8 ![60,0,4] ![(51/3200),0,0] ![(1/3200),1,(1/16)] affine00540
theorem leaf00540_checked : FastNestedCellData.accepts 1 2 4 leaf00540=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (795126047167/1000000000000) (2712305/536870912) (-11355805447/4294967296) 8 8 ![60,0,4] ![(51/3200),0,0] ![(1/3200),1,(1/16)] 45835895932593620821506365849600000000000 415689757361669908651221230643784450048 522797308480529198579974144000000000000 raw00540 affine00540
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00540_raw leaf00540_rectangular
    leaf00540_transform leaf00540_sign leaf00540_log
#print axioms leaf00540_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
