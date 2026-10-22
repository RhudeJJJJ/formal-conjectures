/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00534 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 69708721898922838930708706099200000000000 61322080399818370246107618844118146351104 1081828014618803598303929827328000000000000))
theorem leaf00534_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 69708721898922838930708706099200000000000 61322080399818370246107618844118146351104 1081828014618803598303929827328000000000000 raw00534=true := by decide +kernel
#print axioms leaf00534_raw
theorem leaf00534_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00534=true := by decide +kernel
#print axioms leaf00534_rectangular
def affine00534 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00534 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(49/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00534_transform : affine00534=(NestedInteger.clearedAll 3 raw00534 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(49/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00534_transform
theorem leaf00534_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00534=true := by decide +kernel
#print axioms leaf00534_sign
theorem leaf00534_log : RationalLog.accepts (3575564265/4294967296) (-393678759/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00534_log
def leaf00534 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (56683760793/1000000000000) (3575564265/4294967296) (-393678759/4294967296) 1 8 ![60,0,4] ![(49/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00534
theorem leaf00534_checked : FastNestedCellData.accepts 1 2 4 leaf00534=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (56683760793/1000000000000) (3575564265/4294967296) (-393678759/4294967296) 1 8 ![60,0,4] ![(49/3200),0,(1/2)] ![(1/3200),1,(1/2)] 69708721898922838930708706099200000000000 61322080399818370246107618844118146351104 1081828014618803598303929827328000000000000 raw00534 affine00534
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00534_raw leaf00534_rectangular
    leaf00534_transform leaf00534_sign leaf00534_log
#print axioms leaf00534_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
