/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00453 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 241141532306439353676070912000000000000 256055310419101989340626306143736561664 76514109506396999063166779392000000000000))
theorem leaf00453_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 241141532306439353676070912000000000000 256055310419101989340626306143736561664 76514109506396999063166779392000000000000 raw00453=true := by decide +kernel
#print axioms leaf00453_raw
theorem leaf00453_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00453=true := by decide +kernel
#print axioms leaf00453_rectangular
def affine00453 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00453 (IntegerComputedClassCell.leftNumerator ![(3/16),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/16),0,0] ![(1/64),1,(1/2)]))
theorem leaf00453_transform : affine00453=(NestedInteger.clearedAll 3 raw00453 (IntegerComputedClassCell.leftNumerator ![(3/16),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/16),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00453_transform
theorem leaf00453_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00453=true := by decide +kernel
#print axioms leaf00453_sign
theorem leaf00453_log : RationalLog.accepts (284086571/268435456) (121694723/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00453_log
def leaf00453 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (3346511017/1000000000000) (284086571/268435456) (121694723/4294967296) 0 8 ![52,0,4] ![(3/16),0,0] ![(1/64),1,(1/2)] affine00453
theorem leaf00453_checked : FastNestedCellData.accepts 1 0 4 leaf00453=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (3346511017/1000000000000) (284086571/268435456) (121694723/4294967296) 0 8 ![52,0,4] ![(3/16),0,0] ![(1/64),1,(1/2)] 241141532306439353676070912000000000000 256055310419101989340626306143736561664 76514109506396999063166779392000000000000 raw00453 affine00453
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00453_raw leaf00453_rectangular
    leaf00453_transform leaf00453_sign leaf00453_log
#print axioms leaf00453_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
