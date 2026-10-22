/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00463 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 25337970296664287290064896000000000000 20732008819650161445141371606261563392 230308175096581666124070912000000000000))
theorem leaf00463_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 25337970296664287290064896000000000000 20732008819650161445141371606261563392 230308175096581666124070912000000000000 raw00463=true := by decide +kernel
#print axioms leaf00463_raw
theorem leaf00463_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00463=true := by decide +kernel
#print axioms leaf00463_rectangular
def affine00463 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00463 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00463_transform : affine00463=(NestedInteger.clearedAll 3 raw00463 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00463_transform
theorem leaf00463_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00463=true := by decide +kernel
#print axioms leaf00463_sign
theorem leaf00463_log : RationalLog.accepts (25187529/33554432) (-153985305/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00463_log
def leaf00463 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (45009276833/500000000000) (25187529/33554432) (-153985305/1073741824) 1 8 ![60,0,4] ![(19/1600),0,(1/4)] ![(1/6400),1,(1/4)] affine00463
theorem leaf00463_checked : FastNestedCellData.accepts 1 2 4 leaf00463=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (45009276833/500000000000) (25187529/33554432) (-153985305/1073741824) 1 8 ![60,0,4] ![(19/1600),0,(1/4)] ![(1/6400),1,(1/4)] 25337970296664287290064896000000000000 20732008819650161445141371606261563392 230308175096581666124070912000000000000 raw00463 affine00463
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00463_raw leaf00463_rectangular
    leaf00463_transform leaf00463_sign leaf00463_log
#print axioms leaf00463_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
