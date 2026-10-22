/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00753 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 170138506150847759847836876800000000000 106004973276616738794875464340727660544 448955589371135891308596428800000000000))
theorem leaf00753_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 170138506150847759847836876800000000000 106004973276616738794875464340727660544 448955589371135891308596428800000000000 raw00753=true := by decide +kernel
#print axioms leaf00753_raw
theorem leaf00753_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00753=true := by decide +kernel
#print axioms leaf00753_rectangular
def affine00753 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00753 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/1280),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00753_transform : affine00753=(NestedInteger.clearedAll 3 raw00753 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/1280),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00753_transform
theorem leaf00753_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00753=true := by decide +kernel
#print axioms leaf00753_sign
theorem leaf00753_log : RationalLog.accepts (135302171/268435456) (-183905113/536870912) 1 8=true := by decide +kernel
#print axioms leaf00753_log
def leaf00753 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (23611460863/100000000000) (135302171/268435456) (-183905113/536870912) 1 8 ![60,0,4] ![(43/1280),0,(1/4)] ![(3/6400),1,(1/4)] affine00753
theorem leaf00753_checked : FastNestedCellData.accepts 1 2 4 leaf00753=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (23611460863/100000000000) (135302171/268435456) (-183905113/536870912) 1 8 ![60,0,4] ![(43/1280),0,(1/4)] ![(3/6400),1,(1/4)] 170138506150847759847836876800000000000 106004973276616738794875464340727660544 448955589371135891308596428800000000000 raw00753 affine00753
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00753_raw leaf00753_rectangular
    leaf00753_transform leaf00753_sign leaf00753_log
#print axioms leaf00753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
