/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00060 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 123502048686210534315218540953600000000000 4392471234964607088668941871535357952 26243060284252591745715404800000000000))
theorem leaf00060_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 123502048686210534315218540953600000000000 4392471234964607088668941871535357952 26243060284252591745715404800000000000 raw00060=true := by decide +kernel
#print axioms leaf00060_raw
theorem leaf00060_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00060=true := by decide +kernel
#print axioms leaf00060_rectangular
def affine00060 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00060 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/4000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00060_transform : affine00060=(NestedInteger.clearedAll 3 raw00060 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/4000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00060_transform
theorem leaf00060_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00060=true := by decide +kernel
#print axioms leaf00060_sign
theorem leaf00060_log : RationalLog.accepts (130853/4294967296) (-11165712601/2147483648) 16 8=true := by decide +kernel
#print axioms leaf00060_log
def leaf00060 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33475297373/200000000000) (130853/4294967296) (-11165712601/2147483648) 16 8 ![60,0,4] ![(7/4000),0,0] ![(1/16000),1,(1/16)] affine00060
theorem leaf00060_checked : FastNestedCellData.accepts 1 2 4 leaf00060=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33475297373/200000000000) (130853/4294967296) (-11165712601/2147483648) 16 8 ![60,0,4] ![(7/4000),0,0] ![(1/16000),1,(1/16)] 123502048686210534315218540953600000000000 4392471234964607088668941871535357952 26243060284252591745715404800000000000 raw00060 affine00060
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00060_raw leaf00060_rectangular
    leaf00060_transform leaf00060_sign leaf00060_log
#print axioms leaf00060_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
