/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00610 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1031305882208928485129060771430400000000000 15832651796091965107653201163536184639488 18879680007584713935492743168000000000000))
theorem leaf00610_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1031305882208928485129060771430400000000000 15832651796091965107653201163536184639488 18879680007584713935492743168000000000000 raw00610=true := by decide +kernel
#print axioms leaf00610_raw
theorem leaf00610_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00610=true := by decide +kernel
#print axioms leaf00610_rectangular
def affine00610 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00610 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(131/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00610_transform : affine00610=(NestedInteger.clearedAll 3 raw00610 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(131/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00610_transform
theorem leaf00610_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00610=true := by decide +kernel
#print axioms leaf00610_sign
theorem leaf00610_log : RationalLog.accepts (35862195/4294967296) (-642301039/268435456) 7 8=true := by decide +kernel
#print axioms leaf00610_log
def leaf00610 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (838608058491/1000000000000) (35862195/4294967296) (-642301039/268435456) 7 8 ![60,0,4] ![(131/6400),0,0] ![(3/6400),1,(1/16)] affine00610
theorem leaf00610_checked : FastNestedCellData.accepts 1 2 4 leaf00610=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (838608058491/1000000000000) (35862195/4294967296) (-642301039/268435456) 7 8 ![60,0,4] ![(131/6400),0,0] ![(3/6400),1,(1/16)] 1031305882208928485129060771430400000000000 15832651796091965107653201163536184639488 18879680007584713935492743168000000000000 raw00610 affine00610
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00610_raw leaf00610_rectangular
    leaf00610_transform leaf00610_sign leaf00610_log
#print axioms leaf00610_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
