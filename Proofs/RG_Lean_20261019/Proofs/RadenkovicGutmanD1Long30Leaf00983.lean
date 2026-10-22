/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00983 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7120917752176171490934888857600000000000 4169593278685877201333501222003266289664 9001112728748145589926179635200000000000))
theorem leaf00983_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7120917752176171490934888857600000000000 4169593278685877201333501222003266289664 9001112728748145589926179635200000000000 raw00983=true := by decide +kernel
#print axioms leaf00983_raw
theorem leaf00983_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00983=true := by decide +kernel
#print axioms leaf00983_rectangular
def affine00983 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00983 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00983_transform : affine00983=(NestedInteger.clearedAll 3 raw00983 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00983_transform
theorem leaf00983_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00983=true := by decide +kernel
#print axioms leaf00983_sign
theorem leaf00983_log : RationalLog.accepts (1718718417/4294967296) (-245850657/536870912) 2 8=true := by decide +kernel
#print axioms leaf00983_log
def leaf00983 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (23161543491/50000000000) (1718718417/4294967296) (-245850657/536870912) 2 8 ![60,0,4] ![(1/8),0,(1/4)] ![(1/160),1,(1/4)] affine00983
theorem leaf00983_checked : FastNestedCellData.accepts 1 2 4 leaf00983=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (23161543491/50000000000) (1718718417/4294967296) (-245850657/536870912) 2 8 ![60,0,4] ![(1/8),0,(1/4)] ![(1/160),1,(1/4)] 7120917752176171490934888857600000000000 4169593278685877201333501222003266289664 9001112728748145589926179635200000000000 raw00983 affine00983
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00983_raw leaf00983_rectangular
    leaf00983_transform leaf00983_sign leaf00983_log
#print axioms leaf00983_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
