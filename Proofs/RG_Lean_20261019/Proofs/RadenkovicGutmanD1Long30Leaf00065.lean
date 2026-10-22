/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00065 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5107561585884976628774643695616000000000 200494716136187267089314523052507136 1158587996876232036293017600000000000))
theorem leaf00065_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5107561585884976628774643695616000000000 200494716136187267089314523052507136 1158587996876232036293017600000000000 raw00065=true := by decide +kernel
#print axioms leaf00065_raw
theorem leaf00065_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00065=true := by decide +kernel
#print axioms leaf00065_rectangular
def affine00065 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00065 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/16000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00065_transform : affine00065=(NestedInteger.clearedAll 3 raw00065 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/16000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00065_transform
theorem leaf00065_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00065=true := by decide +kernel
#print axioms leaf00065_sign
theorem leaf00065_log : RationalLog.accepts (143725/4294967296) (-5532483199/1073741824) 15 8=true := by decide +kernel
#print axioms leaf00065_log
def leaf00065 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34610183547/200000000000) (143725/4294967296) (-5532483199/1073741824) 15 8 ![60,0,4] ![(29/16000),0,0] ![(1/16000),1,(1/16)] affine00065
theorem leaf00065_checked : FastNestedCellData.accepts 1 2 4 leaf00065=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34610183547/200000000000) (143725/4294967296) (-5532483199/1073741824) 15 8 ![60,0,4] ![(29/16000),0,0] ![(1/16000),1,(1/16)] 5107561585884976628774643695616000000000 200494716136187267089314523052507136 1158587996876232036293017600000000000 raw00065 affine00065
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00065_raw leaf00065_rectangular
    leaf00065_transform leaf00065_sign leaf00065_log
#print axioms leaf00065_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
