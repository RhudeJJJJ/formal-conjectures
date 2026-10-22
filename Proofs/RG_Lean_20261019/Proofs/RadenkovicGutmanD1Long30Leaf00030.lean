/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00030 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3193267448796583387251867648000000000000 57383226178910034986074210616475648 431626568803350910861312000000000000))
theorem leaf00030_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3193267448796583387251867648000000000000 57383226178910034986074210616475648 431626568803350910861312000000000000 raw00030=true := by decide +kernel
#print axioms leaf00030_raw
theorem leaf00030_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00030=true := by decide +kernel
#print axioms leaf00030_rectangular
def affine00030 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00030 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/8000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00030_transform : affine00030=(NestedInteger.clearedAll 3 raw00030 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/8000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00030_transform
theorem leaf00030_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00030=true := by decide +kernel
#print axioms leaf00030_sign
theorem leaf00030_log : RationalLog.accepts (17031/1073741824) (-23733184375/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00030_log
def leaf00030 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33236616051/250000000000) (17031/1073741824) (-23733184375/4294967296) 16 8 ![60,0,4] ![(11/8000),0,0] ![(1/16000),1,(1/16)] affine00030
theorem leaf00030_checked : FastNestedCellData.accepts 1 2 4 leaf00030=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33236616051/250000000000) (17031/1073741824) (-23733184375/4294967296) 16 8 ![60,0,4] ![(11/8000),0,0] ![(1/16000),1,(1/16)] 3193267448796583387251867648000000000000 57383226178910034986074210616475648 431626568803350910861312000000000000 raw00030 affine00030
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00030_raw leaf00030_rectangular
    leaf00030_transform leaf00030_sign leaf00030_log
#print axioms leaf00030_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
