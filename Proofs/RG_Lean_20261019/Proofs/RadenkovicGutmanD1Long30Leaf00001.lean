/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00001 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 149865564553803166430198235136000000000000 138671742191924522092173527044625805606912 4267228008792341602467229728768000000000000))
theorem leaf00001_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 149865564553803166430198235136000000000000 138671742191924522092173527044625805606912 4267228008792341602467229728768000000000000 raw00001=true := by decide +kernel
#print axioms leaf00001_raw
theorem leaf00001_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00001=true := by decide +kernel
#print axioms leaf00001_rectangular
def affine00001 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00001 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00001_transform : affine00001=(NestedInteger.clearedAll 3 raw00001 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00001_transform
theorem leaf00001_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00001=true := by decide +kernel
#print axioms leaf00001_sign
theorem leaf00001_log : RationalLog.accepts (3849082473/4294967296) (-235383871/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00001_log
def leaf00001 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16248457067/500000000000) (3849082473/4294967296) (-235383871/4294967296) 1 8 ![60,0,4] ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)] affine00001
theorem leaf00001_checked : FastNestedCellData.accepts 1 2 4 leaf00001=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16248457067/500000000000) (3849082473/4294967296) (-235383871/4294967296) 1 8 ![60,0,4] ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)] 149865564553803166430198235136000000000000 138671742191924522092173527044625805606912 4267228008792341602467229728768000000000000 raw00001 affine00001
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00001_raw leaf00001_rectangular
    leaf00001_transform leaf00001_sign leaf00001_log
#print axioms leaf00001_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
