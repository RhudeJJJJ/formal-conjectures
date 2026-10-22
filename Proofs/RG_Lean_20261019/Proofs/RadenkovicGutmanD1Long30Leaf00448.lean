/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00448 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 249506976915314883165369139200000000000 205626434774600322752419560823342497792 2375395885700404246399575654400000000000))
theorem leaf00448_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 249506976915314883165369139200000000000 205626434774600322752419560823342497792 2375395885700404246399575654400000000000 raw00448=true := by decide +kernel
#print axioms leaf00448_raw
theorem leaf00448_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00448=true := by decide +kernel
#print axioms leaf00448_rectangular
def affine00448 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00448 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00448_transform : affine00448=(NestedInteger.clearedAll 3 raw00448 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00448_transform
theorem leaf00448_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00448=true := by decide +kernel
#print axioms leaf00448_sign
theorem leaf00448_log : RationalLog.accepts (203601217/268435456) (-296832977/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00448_log
def leaf00448 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17313024411/200000000000) (203601217/268435456) (-296832977/2147483648) 1 8 ![60,0,4] ![(73/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00448
theorem leaf00448_checked : FastNestedCellData.accepts 1 2 4 leaf00448=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17313024411/200000000000) (203601217/268435456) (-296832977/2147483648) 1 8 ![60,0,4] ![(73/6400),0,(1/4)] ![(1/6400),1,(1/4)] 249506976915314883165369139200000000000 205626434774600322752419560823342497792 2375395885700404246399575654400000000000 raw00448 affine00448
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00448_raw leaf00448_rectangular
    leaf00448_transform leaf00448_sign leaf00448_log
#print axioms leaf00448_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
