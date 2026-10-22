/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00003 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2264469416826246735702523904000000000000 2221403756572509308896022171949610303488 282748813291148279919534931968000000000000))
theorem leaf00003_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2264469416826246735702523904000000000000 2221403756572509308896022171949610303488 282748813291148279919534931968000000000000 raw00003=true := by decide +kernel
#print axioms leaf00003_raw
theorem leaf00003_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00003=true := by decide +kernel
#print axioms leaf00003_rectangular
def affine00003 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00003 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00003_transform : affine00003=(NestedInteger.clearedAll 3 raw00003 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00003_transform
theorem leaf00003_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00003=true := by decide +kernel
#print axioms leaf00003_sign
theorem leaf00003_log : RationalLog.accepts (2090221091/2147483648) (-58039895/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00003_log
def leaf00003 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1964114129/250000000000) (2090221091/2147483648) (-58039895/4294967296) 1 8 ![60,0,4] ![(1/1000),0,(1/4)] ![(1/16000),1,(1/4)] affine00003
theorem leaf00003_checked : FastNestedCellData.accepts 1 2 4 leaf00003=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1964114129/250000000000) (2090221091/2147483648) (-58039895/4294967296) 1 8 ![60,0,4] ![(1/1000),0,(1/4)] ![(1/16000),1,(1/4)] 2264469416826246735702523904000000000000 2221403756572509308896022171949610303488 282748813291148279919534931968000000000000 raw00003 affine00003
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00003_raw leaf00003_rectangular
    leaf00003_transform leaf00003_sign leaf00003_log
#print axioms leaf00003_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
