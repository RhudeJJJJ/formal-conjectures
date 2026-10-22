/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00200 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 433151911675660087390659149824000000000000 173033393146765048131919279913357541376 460563406501540592116301824000000000000))
theorem leaf00200_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 433151911675660087390659149824000000000000 173033393146765048131919279913357541376 460563406501540592116301824000000000000 raw00200=true := by decide +kernel
#print axioms leaf00200_raw
theorem leaf00200_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00200=true := by decide +kernel
#print axioms leaf00200_rectangular
def affine00200 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00200 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/4000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00200_transform : affine00200=(NestedInteger.clearedAll 3 raw00200 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/4000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00200_transform
theorem leaf00200_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00200=true := by decide +kernel
#print axioms leaf00200_sign
theorem leaf00200_log : RationalLog.accepts (1247171/4294967296) (-8744898763/2147483648) 12 8=true := by decide +kernel
#print axioms leaf00200_log
def leaf00200 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (93924848731/250000000000) (1247171/4294967296) (-8744898763/2147483648) 12 8 ![60,0,4] ![(17/4000),0,0] ![(3/32000),1,(1/16)] affine00200
theorem leaf00200_checked : FastNestedCellData.accepts 1 2 4 leaf00200=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (93924848731/250000000000) (1247171/4294967296) (-8744898763/2147483648) 12 8 ![60,0,4] ![(17/4000),0,0] ![(3/32000),1,(1/16)] 433151911675660087390659149824000000000000 173033393146765048131919279913357541376 460563406501540592116301824000000000000 raw00200 affine00200
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00200_raw leaf00200_rectangular
    leaf00200_transform leaf00200_sign leaf00200_log
#print axioms leaf00200_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
