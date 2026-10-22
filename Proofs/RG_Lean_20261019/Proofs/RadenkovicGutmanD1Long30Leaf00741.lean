/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00741 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 46280140696656699268523884544000000000000 12184944651639492894917218892706251538432 18971804792846886551062315008000000000000))
theorem leaf00741_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 46280140696656699268523884544000000000000 12184944651639492894917218892706251538432 18971804792846886551062315008000000000000 raw00741=true := by decide +kernel
#print axioms leaf00741_raw
theorem leaf00741_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00741=true := by decide +kernel
#print axioms leaf00741_rectangular
def affine00741 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00741 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(209/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00741_transform : affine00741=(NestedInteger.clearedAll 3 raw00741 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(209/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00741_transform
theorem leaf00741_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00741=true := by decide +kernel
#print axioms leaf00741_sign
theorem leaf00741_log : RationalLog.accepts (688565497/4294967296) (-1965579785/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00741_log
def leaf00741 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (40141623269/62500000000) (688565497/4294967296) (-1965579785/2147483648) 3 8 ![60,0,4] ![(209/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00741
theorem leaf00741_checked : FastNestedCellData.accepts 1 2 4 leaf00741=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (40141623269/62500000000) (688565497/4294967296) (-1965579785/2147483648) 3 8 ![60,0,4] ![(209/6400),0,(1/16)] ![(3/6400),1,(1/16)] 46280140696656699268523884544000000000000 12184944651639492894917218892706251538432 18971804792846886551062315008000000000000 raw00741 affine00741
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00741_raw leaf00741_rectangular
    leaf00741_transform leaf00741_sign leaf00741_log
#print axioms leaf00741_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
