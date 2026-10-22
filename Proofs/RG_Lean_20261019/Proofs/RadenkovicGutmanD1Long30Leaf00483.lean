/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00483 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 363587182818774883060468940800000000000 294676132788488756821975966471321288704 3114690381844121368898673049600000000000))
theorem leaf00483_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 363587182818774883060468940800000000000 294676132788488756821975966471321288704 3114690381844121368898673049600000000000 raw00483=true := by decide +kernel
#print axioms leaf00483_raw
theorem leaf00483_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00483=true := by decide +kernel
#print axioms leaf00483_rectangular
def affine00483 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00483 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00483_transform : affine00483=(NestedInteger.clearedAll 3 raw00483 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00483_transform
theorem leaf00483_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00483=true := by decide +kernel
#print axioms leaf00483_sign
theorem leaf00483_log : RationalLog.accepts (3180075627/4294967296) (-645402543/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00483_log
def leaf00483 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2365212081/25000000000) (3180075627/4294967296) (-645402543/4294967296) 1 8 ![60,0,4] ![(1/80),0,(1/4)] ![(1/6400),1,(1/4)] affine00483
theorem leaf00483_checked : FastNestedCellData.accepts 1 2 4 leaf00483=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2365212081/25000000000) (3180075627/4294967296) (-645402543/4294967296) 1 8 ![60,0,4] ![(1/80),0,(1/4)] ![(1/6400),1,(1/4)] 363587182818774883060468940800000000000 294676132788488756821975966471321288704 3114690381844121368898673049600000000000 raw00483 affine00483
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00483_raw leaf00483_rectangular
    leaf00483_transform leaf00483_sign leaf00483_log
#print axioms leaf00483_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
