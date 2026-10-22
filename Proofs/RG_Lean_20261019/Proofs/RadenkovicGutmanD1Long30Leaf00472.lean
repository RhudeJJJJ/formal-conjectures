/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00472 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 53216191277700929724467904512000000000000 35588552805623399060491985207045860098048 192755282096976230233172606976000000000000))
theorem leaf00472_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 53216191277700929724467904512000000000000 35588552805623399060491985207045860098048 192755282096976230233172606976000000000000 raw00472=true := by decide +kernel
#print axioms leaf00472_raw
theorem leaf00472_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00472=true := by decide +kernel
#print axioms leaf00472_rectangular
def affine00472 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00472 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(39/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00472_transform : affine00472=(NestedInteger.clearedAll 3 raw00472 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(39/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00472_transform
theorem leaf00472_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00472=true := by decide +kernel
#print axioms leaf00472_sign
theorem leaf00472_log : RationalLog.accepts (303077301/536870912) (-1227866303/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00472_log
def leaf00472 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (184630752623/1000000000000) (303077301/536870912) (-1227866303/4294967296) 1 8 ![60,0,4] ![(39/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00472
theorem leaf00472_checked : FastNestedCellData.accepts 1 2 4 leaf00472=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (184630752623/1000000000000) (303077301/536870912) (-1227866303/4294967296) 1 8 ![60,0,4] ![(39/3200),0,(1/8)] ![(1/6400),1,(1/8)] 53216191277700929724467904512000000000000 35588552805623399060491985207045860098048 192755282096976230233172606976000000000000 raw00472 affine00472
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00472_raw leaf00472_rectangular
    leaf00472_transform leaf00472_sign leaf00472_log
#print axioms leaf00472_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
