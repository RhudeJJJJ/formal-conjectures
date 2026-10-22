/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00031 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 816912912127411933430622978048000000000000 736304732755524287888780741780724906983424 16626527459372370428121063620608000000000000))
theorem leaf00031_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 816912912127411933430622978048000000000000 736304732755524287888780741780724906983424 16626527459372370428121063620608000000000000 raw00031=true := by decide +kernel
#print axioms leaf00031_raw
theorem leaf00031_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00031=true := by decide +kernel
#print axioms leaf00031_rectangular
def affine00031 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00031 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/8000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00031_transform : affine00031=(NestedInteger.clearedAll 3 raw00031 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/8000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00031_transform
theorem leaf00031_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00031=true := by decide +kernel
#print axioms leaf00031_sign
theorem leaf00031_log : RationalLog.accepts (3707000791/4294967296) (-4939911/67108864) 1 8=true := by decide +kernel
#print axioms leaf00031_log
def leaf00031 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (44284937703/1000000000000) (3707000791/4294967296) (-4939911/67108864) 1 8 ![60,0,4] ![(11/8000),0,(1/16)] ![(1/16000),1,(1/16)] affine00031
theorem leaf00031_checked : FastNestedCellData.accepts 1 2 4 leaf00031=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (44284937703/1000000000000) (3707000791/4294967296) (-4939911/67108864) 1 8 ![60,0,4] ![(11/8000),0,(1/16)] ![(1/16000),1,(1/16)] 816912912127411933430622978048000000000000 736304732755524287888780741780724906983424 16626527459372370428121063620608000000000000 raw00031 affine00031
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00031_raw leaf00031_rectangular
    leaf00031_transform leaf00031_sign leaf00031_log
#print axioms leaf00031_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
