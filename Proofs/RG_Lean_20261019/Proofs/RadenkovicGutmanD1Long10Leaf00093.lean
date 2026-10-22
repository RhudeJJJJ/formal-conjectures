/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00093 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 264339445652449797022416896000000000 315371177026048739930402910633984 1375497368654388400226304000000000))
theorem leaf00093_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 264339445652449797022416896000000000 315371177026048739930402910633984 1375497368654388400226304000000000 raw00093=true := by decide +kernel
#print axioms leaf00093_raw
theorem leaf00093_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00093=true := by decide +kernel
#print axioms leaf00093_rectangular
def affine00093 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00093 (IntegerComputedClassCell.leftNumerator ![(1/100),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/100),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00093_transform : affine00093=(NestedInteger.clearedAll 3 raw00093 (IntegerComputedClassCell.leftNumerator ![(1/100),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/100),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00093_transform
theorem leaf00093_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00093=true := by decide +kernel
#print axioms leaf00093_sign
theorem leaf00093_log : RationalLog.accepts (1042101/1073741824) (-14898524661/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00093_log
def leaf00093 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (229277921/1000000000) (1042101/1073741824) (-14898524661/4294967296) 11 8 ![52,0,4] ![(1/100),0,0] ![(1/3200),1,(1/4)] affine00093
theorem leaf00093_checked : FastNestedCellData.accepts 1 0 4 leaf00093=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (229277921/1000000000) (1042101/1073741824) (-14898524661/4294967296) 11 8 ![52,0,4] ![(1/100),0,0] ![(1/3200),1,(1/4)] 264339445652449797022416896000000000 315371177026048739930402910633984 1375497368654388400226304000000000 raw00093 affine00093
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00093_raw leaf00093_rectangular
    leaf00093_transform leaf00093_sign leaf00093_log
#print axioms leaf00093_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
