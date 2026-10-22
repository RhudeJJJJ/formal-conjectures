/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00970 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 30059667956841076981500372582400000000000 10655950978952177304703888756362344136704 14215754858618592375200546816000000000000))
theorem leaf00970_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 30059667956841076981500372582400000000000 10655950978952177304703888756362344136704 14215754858618592375200546816000000000000 raw00970=true := by decide +kernel
#print axioms leaf00970_raw
theorem leaf00970_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00970=true := by decide +kernel
#print axioms leaf00970_rectangular
def affine00970 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00970 (IntegerComputedClassCell.leftNumerator ![(9/80),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/80),0,0] ![(1/160),1,(1/16)]))
theorem leaf00970_transform : affine00970=(NestedInteger.clearedAll 3 raw00970 (IntegerComputedClassCell.leftNumerator ![(9/80),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/80),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00970_transform
theorem leaf00970_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00970=true := by decide +kernel
#print axioms leaf00970_sign
theorem leaf00970_log : RationalLog.accepts (435113195/2147483648) (-107135669/134217728) 3 8=true := by decide +kernel
#print axioms leaf00970_log
def leaf00970 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (749587417969/1000000000000) (435113195/2147483648) (-107135669/134217728) 3 8 ![60,0,4] ![(9/80),0,0] ![(1/160),1,(1/16)] affine00970
theorem leaf00970_checked : FastNestedCellData.accepts 1 2 4 leaf00970=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (749587417969/1000000000000) (435113195/2147483648) (-107135669/134217728) 3 8 ![60,0,4] ![(9/80),0,0] ![(1/160),1,(1/16)] 30059667956841076981500372582400000000000 10655950978952177304703888756362344136704 14215754858618592375200546816000000000000 raw00970 affine00970
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00970_raw leaf00970_rectangular
    leaf00970_transform leaf00970_sign leaf00970_log
#print axioms leaf00970_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
