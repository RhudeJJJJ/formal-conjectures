/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00916 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4033371850986321472103907328000000000000 1225036420444837033465179849931697946624 1683515589577682825118744576000000000000))
theorem leaf00916_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4033371850986321472103907328000000000000 1225036420444837033465179849931697946624 1683515589577682825118744576000000000000 raw00916=true := by decide +kernel
#print axioms leaf00916_raw
theorem leaf00916_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00916=true := by decide +kernel
#print axioms leaf00916_rectangular
def affine00916 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00916 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00916_transform : affine00916=(NestedInteger.clearedAll 3 raw00916 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00916_transform
theorem leaf00916_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00916=true := by decide +kernel
#print axioms leaf00916_sign
theorem leaf00916_log : RationalLog.accepts (94382379/536870912) (-116662273/134217728) 3 8=true := by decide +kernel
#print axioms leaf00916_log
def leaf00916 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (363832811537/500000000000) (94382379/536870912) (-116662273/134217728) 3 8 ![60,0,4] ![(3/40),0,(1/16)] ![(1/320),1,(1/16)] affine00916
theorem leaf00916_checked : FastNestedCellData.accepts 1 2 4 leaf00916=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (363832811537/500000000000) (94382379/536870912) (-116662273/134217728) 3 8 ![60,0,4] ![(3/40),0,(1/16)] ![(1/320),1,(1/16)] 4033371850986321472103907328000000000000 1225036420444837033465179849931697946624 1683515589577682825118744576000000000000 raw00916 affine00916
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00916_raw leaf00916_rectangular
    leaf00916_transform leaf00916_sign leaf00916_log
#print axioms leaf00916_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
