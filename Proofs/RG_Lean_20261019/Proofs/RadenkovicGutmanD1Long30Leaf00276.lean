/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00276 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 853492283012168658712526848000000000000 558365111678698974476443531727148679168 2946310070921896600205787136000000000000))
theorem leaf00276_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 853492283012168658712526848000000000000 558365111678698974476443531727148679168 2946310070921896600205787136000000000000 raw00276=true := by decide +kernel
#print axioms leaf00276_raw
theorem leaf00276_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00276=true := by decide +kernel
#print axioms leaf00276_rectangular
def affine00276 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00276 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00276_transform : affine00276=(NestedInteger.clearedAll 3 raw00276 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00276_transform
theorem leaf00276_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00276=true := by decide +kernel
#print axioms leaf00276_sign
theorem leaf00276_log : RationalLog.accepts (147634967/268435456) (-641955583/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00276_log
def leaf00276 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (47378339197/250000000000) (147634967/268435456) (-641955583/2147483648) 1 8 ![60,0,4] ![(39/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00276
theorem leaf00276_checked : FastNestedCellData.accepts 1 2 4 leaf00276=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (47378339197/250000000000) (147634967/268435456) (-641955583/2147483648) 1 8 ![60,0,4] ![(39/6400),0,(1/16)] ![(1/6400),1,(1/16)] 853492283012168658712526848000000000000 558365111678698974476443531727148679168 2946310070921896600205787136000000000000 raw00276 affine00276
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00276_raw leaf00276_rectangular
    leaf00276_transform leaf00276_sign leaf00276_log
#print axioms leaf00276_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
