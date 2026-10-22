/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00135 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 258646779719258708148530603622400000000000 42156299844975677746020444103023525888 150329819528181199033860096000000000000))
theorem leaf00135_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 258646779719258708148530603622400000000000 42156299844975677746020444103023525888 150329819528181199033860096000000000000 raw00135=true := by decide +kernel
#print axioms leaf00135_raw
theorem leaf00135_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00135=true := by decide +kernel
#print axioms leaf00135_rectangular
def affine00135 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00135 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(97/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00135_transform : affine00135=(NestedInteger.clearedAll 3 raw00135 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(97/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00135_transform
theorem leaf00135_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00135=true := by decide +kernel
#print axioms leaf00135_sign
theorem leaf00135_log : RationalLog.accepts (546715/4294967296) (-19260838971/4294967296) 13 8=true := by decide +kernel
#print axioms leaf00135_log
def leaf00135 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (140212700239/500000000000) (546715/4294967296) (-19260838971/4294967296) 13 8 ![60,0,4] ![(97/32000),0,0] ![(3/32000),1,(1/16)] affine00135
theorem leaf00135_checked : FastNestedCellData.accepts 1 2 4 leaf00135=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (140212700239/500000000000) (546715/4294967296) (-19260838971/4294967296) 13 8 ![60,0,4] ![(97/32000),0,0] ![(3/32000),1,(1/16)] 258646779719258708148530603622400000000000 42156299844975677746020444103023525888 150329819528181199033860096000000000000 raw00135 affine00135
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00135_raw leaf00135_rectangular
    leaf00135_transform leaf00135_sign leaf00135_log
#print axioms leaf00135_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
