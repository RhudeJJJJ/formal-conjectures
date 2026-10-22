/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00918 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 39081193831959420856315150336000000000000 20542039573901351246459246466193806065664 50500332024717992895291850752000000000000))
theorem leaf00918_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 39081193831959420856315150336000000000000 20542039573901351246459246466193806065664 50500332024717992895291850752000000000000 raw00918=true := by decide +kernel
#print axioms leaf00918_raw
theorem leaf00918_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00918=true := by decide +kernel
#print axioms leaf00918_rectangular
def affine00918 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00918 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00918_transform : affine00918=(NestedInteger.clearedAll 3 raw00918 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00918_transform
theorem leaf00918_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00918=true := by decide +kernel
#print axioms leaf00918_sign
theorem leaf00918_log : RationalLog.accepts (200596059/536870912) (-2114121377/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00918_log
def leaf00918 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (406770386457/1000000000000) (200596059/536870912) (-2114121377/4294967296) 2 8 ![60,0,4] ![(3/40),0,(1/4)] ![(1/320),1,(1/4)] affine00918
theorem leaf00918_checked : FastNestedCellData.accepts 1 2 4 leaf00918=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (406770386457/1000000000000) (200596059/536870912) (-2114121377/4294967296) 2 8 ![60,0,4] ![(3/40),0,(1/4)] ![(1/320),1,(1/4)] 39081193831959420856315150336000000000000 20542039573901351246459246466193806065664 50500332024717992895291850752000000000000 raw00918 affine00918
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00918_raw leaf00918_rectangular
    leaf00918_transform leaf00918_sign leaf00918_log
#print axioms leaf00918_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
