/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00273 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1348755288183626076701725818880000000000 1213370844971018132793268695741331668992 26552174900547308209621214167040000000000))
theorem leaf00273_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1348755288183626076701725818880000000000 1213370844971018132793268695741331668992 26552174900547308209621214167040000000000 raw00273=true := by decide +kernel
#print axioms leaf00273_raw
theorem leaf00273_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00273=true := by decide +kernel
#print axioms leaf00273_rectangular
def affine00273 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00273 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00273_transform : affine00273=(NestedInteger.clearedAll 3 raw00273 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00273_transform
theorem leaf00273_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00273=true := by decide +kernel
#print axioms leaf00273_sign
theorem leaf00273_log : RationalLog.accepts (3694997443/4294967296) (-20194949/268435456) 1 8=true := by decide +kernel
#print axioms leaf00273_log
def leaf00273 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1827904267/40000000000) (3694997443/4294967296) (-20194949/268435456) 1 8 ![60,0,4] ![(19/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00273
theorem leaf00273_checked : FastNestedCellData.accepts 1 2 4 leaf00273=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1827904267/40000000000) (3694997443/4294967296) (-20194949/268435456) 1 8 ![60,0,4] ![(19/3200),0,(1/4)] ![(1/6400),1,(1/4)] 1348755288183626076701725818880000000000 1213370844971018132793268695741331668992 26552174900547308209621214167040000000000 raw00273 affine00273
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00273_raw leaf00273_rectangular
    leaf00273_transform leaf00273_sign leaf00273_log
#print axioms leaf00273_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
