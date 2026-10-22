/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00911 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 13448306402443535790779477786624000000000000 3971031418847383677316496648715383397679104 5446975857036357131433658023936000000000000))
theorem leaf00911_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 13448306402443535790779477786624000000000000 3971031418847383677316496648715383397679104 5446975857036357131433658023936000000000000 raw00911=true := by decide +kernel
#print axioms leaf00911_raw
theorem leaf00911_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00911=true := by decide +kernel
#print axioms leaf00911_rectangular
def affine00911 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00911 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00911_transform : affine00911=(NestedInteger.clearedAll 3 raw00911 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00911_transform
theorem leaf00911_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00911=true := by decide +kernel
#print axioms leaf00911_sign
theorem leaf00911_log : RationalLog.accepts (733486319/4294967296) (-948860455/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00911_log
def leaf00911 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (729034150889/1000000000000) (733486319/4294967296) (-948860455/1073741824) 3 8 ![60,0,4] ![(23/320),0,(1/16)] ![(1/320),1,(1/16)] affine00911
theorem leaf00911_checked : FastNestedCellData.accepts 1 2 4 leaf00911=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (729034150889/1000000000000) (733486319/4294967296) (-948860455/1073741824) 3 8 ![60,0,4] ![(23/320),0,(1/16)] ![(1/320),1,(1/16)] 13448306402443535790779477786624000000000000 3971031418847383677316496648715383397679104 5446975857036357131433658023936000000000000 raw00911 affine00911
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00911_raw leaf00911_rectangular
    leaf00911_transform leaf00911_sign leaf00911_log
#print axioms leaf00911_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
