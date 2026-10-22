/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00436 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 191718831242960890645417295872000000000000 215417094965310698494936909926506633887744 20726936389943030115075968991232000000000000))
theorem leaf00436_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 191718831242960890645417295872000000000000 215417094965310698494936909926506633887744 20726936389943030115075968991232000000000000 raw00436=true := by decide +kernel
#print axioms leaf00436_raw
theorem leaf00436_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00436=true := by decide +kernel
#print axioms leaf00436_rectangular
def affine00436 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00436 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/32),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf00436_transform : affine00436=(NestedInteger.clearedAll 3 raw00436 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/32),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00436_transform
theorem leaf00436_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00436=true := by decide +kernel
#print axioms leaf00436_sign
theorem leaf00436_log : RationalLog.accepts (4776226151/4294967296) (228077335/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00436_log
def leaf00436 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (10393098667/1000000000000) (4776226151/4294967296) (228077335/4294967296) 0 8 ![52,0,4] ![(9/32),0,(1/2)] ![(1/32),1,(1/4)] affine00436
theorem leaf00436_checked : FastNestedCellData.accepts 1 0 4 leaf00436=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (10393098667/1000000000000) (4776226151/4294967296) (228077335/4294967296) 0 8 ![52,0,4] ![(9/32),0,(1/2)] ![(1/32),1,(1/4)] 191718831242960890645417295872000000000000 215417094965310698494936909926506633887744 20726936389943030115075968991232000000000000 raw00436 affine00436
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00436_raw leaf00436_rectangular
    leaf00436_transform leaf00436_sign leaf00436_log
#print axioms leaf00436_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
