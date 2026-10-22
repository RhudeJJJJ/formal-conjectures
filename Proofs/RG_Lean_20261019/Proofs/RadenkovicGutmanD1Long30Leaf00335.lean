/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00335 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10941209871020249251274842701824000000000000 20930898329765395666358459490224798957568 35289234853696591169178304512000000000000))
theorem leaf00335_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10941209871020249251274842701824000000000000 20930898329765395666358459490224798957568 35289234853696591169178304512000000000000 raw00335=true := by decide +kernel
#print axioms leaf00335_raw
theorem leaf00335_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00335=true := by decide +kernel
#print axioms leaf00335_rectangular
def affine00335 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00335 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(51/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00335_transform : affine00335=(NestedInteger.clearedAll 3 raw00335 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(51/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00335_transform
theorem leaf00335_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00335=true := by decide +kernel
#print axioms leaf00335_sign
theorem leaf00335_log : RationalLog.accepts (5157423/4294967296) (-14441317179/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00335_log
def leaf00335 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (593124175589/1000000000000) (5157423/4294967296) (-14441317179/4294967296) 10 8 ![60,0,4] ![(51/6400),0,0] ![(1/6400),1,(1/16)] affine00335
theorem leaf00335_checked : FastNestedCellData.accepts 1 2 4 leaf00335=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (593124175589/1000000000000) (5157423/4294967296) (-14441317179/4294967296) 10 8 ![60,0,4] ![(51/6400),0,0] ![(1/6400),1,(1/16)] 10941209871020249251274842701824000000000000 20930898329765395666358459490224798957568 35289234853696591169178304512000000000000 raw00335 affine00335
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00335_raw leaf00335_rectangular
    leaf00335_transform leaf00335_sign leaf00335_log
#print axioms leaf00335_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
