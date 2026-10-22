/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00841 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 109976009768689302739059998720000000000 27919035418105451136431892258984296448 39024821733534344703765381120000000000))
theorem leaf00841_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 109976009768689302739059998720000000000 27919035418105451136431892258984296448 39024821733534344703765381120000000000 raw00841=true := by decide +kernel
#print axioms leaf00841_raw
theorem leaf00841_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00841=true := by decide +kernel
#print axioms leaf00841_rectangular
def affine00841 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00841 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00841_transform : affine00841=(NestedInteger.clearedAll 3 raw00841 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00841_transform
theorem leaf00841_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00841=true := by decide +kernel
#print axioms leaf00841_sign
theorem leaf00841_log : RationalLog.accepts (79451577/536870912) (-4103003703/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00841_log
def leaf00841 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (28616694891/40000000000) (79451577/536870912) (-4103003703/4294967296) 3 8 ![60,0,4] ![(1/20),0,(1/16)] ![(1/640),1,(1/16)] affine00841
theorem leaf00841_checked : FastNestedCellData.accepts 1 2 4 leaf00841=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (28616694891/40000000000) (79451577/536870912) (-4103003703/4294967296) 3 8 ![60,0,4] ![(1/20),0,(1/16)] ![(1/640),1,(1/16)] 109976009768689302739059998720000000000 27919035418105451136431892258984296448 39024821733534344703765381120000000000 raw00841 affine00841
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00841_raw leaf00841_rectangular
    leaf00841_transform leaf00841_sign leaf00841_log
#print axioms leaf00841_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
