/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00833 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 469227180057706639168372736000000000000 262681690559744659938808246993422385152 840398293193805968466509824000000000000))
theorem leaf00833_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 469227180057706639168372736000000000000 262681690559744659938808246993422385152 840398293193805968466509824000000000000 raw00833=true := by decide +kernel
#print axioms leaf00833_raw
theorem leaf00833_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00833=true := by decide +kernel
#print axioms leaf00833_rectangular
def affine00833 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00833 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00833_transform : affine00833=(NestedInteger.clearedAll 3 raw00833 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00833_transform
theorem leaf00833_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00833=true := by decide +kernel
#print axioms leaf00833_sign
theorem leaf00833_log : RationalLog.accepts (228978483/536870912) (-1829934539/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00833_log
def leaf00833 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (39071011431/125000000000) (228978483/536870912) (-1829934539/4294967296) 2 8 ![60,0,4] ![(77/1600),0,(1/4)] ![(3/3200),1,(1/4)] affine00833
theorem leaf00833_checked : FastNestedCellData.accepts 1 2 4 leaf00833=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (39071011431/125000000000) (228978483/536870912) (-1829934539/4294967296) 2 8 ![60,0,4] ![(77/1600),0,(1/4)] ![(3/3200),1,(1/4)] 469227180057706639168372736000000000000 262681690559744659938808246993422385152 840398293193805968466509824000000000000 raw00833 affine00833
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00833_raw leaf00833_rectangular
    leaf00833_transform leaf00833_sign leaf00833_log
#print axioms leaf00833_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
