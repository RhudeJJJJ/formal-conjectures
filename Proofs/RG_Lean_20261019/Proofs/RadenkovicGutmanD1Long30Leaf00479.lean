/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00479 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 280643560713828109632118194176000000000000 253005095239132094751407326671086322450432 5543354506750809763790668693504000000000000))
theorem leaf00479_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 280643560713828109632118194176000000000000 253005095239132094751407326671086322450432 5543354506750809763790668693504000000000000 raw00479=true := by decide +kernel
#print axioms leaf00479_raw
theorem leaf00479_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00479=true := by decide +kernel
#print axioms leaf00479_rectangular
def affine00479 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00479 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(79/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00479_transform : affine00479=(NestedInteger.clearedAll 3 raw00479 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(79/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00479_transform
theorem leaf00479_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00479=true := by decide +kernel
#print axioms leaf00479_sign
theorem leaf00479_log : RationalLog.accepts (3702980109/4294967296) (-318484769/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00479_log
def leaf00479 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (45641153733/1000000000000) (3702980109/4294967296) (-318484769/4294967296) 1 8 ![60,0,4] ![(79/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00479
theorem leaf00479_checked : FastNestedCellData.accepts 1 2 4 leaf00479=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (45641153733/1000000000000) (3702980109/4294967296) (-318484769/4294967296) 1 8 ![60,0,4] ![(79/6400),0,(1/2)] ![(1/6400),1,(1/2)] 280643560713828109632118194176000000000000 253005095239132094751407326671086322450432 5543354506750809763790668693504000000000000 raw00479 affine00479
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00479_raw leaf00479_rectangular
    leaf00479_transform leaf00479_sign leaf00479_log
#print axioms leaf00479_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
