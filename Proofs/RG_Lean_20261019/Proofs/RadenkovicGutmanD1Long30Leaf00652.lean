/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00652 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1551979541165784577744933224448000000000000 774342637891303537006358026437865024520192 2300948576907847533382458146816000000000000))
theorem leaf00652_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1551979541165784577744933224448000000000000 774342637891303537006358026437865024520192 2300948576907847533382458146816000000000000 raw00652=true := by decide +kernel
#print axioms leaf00652_raw
theorem leaf00652_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00652=true := by decide +kernel
#print axioms leaf00652_rectangular
def affine00652 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00652 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/1280),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00652_transform : affine00652=(NestedInteger.clearedAll 3 raw00652 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/1280),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00652_transform
theorem leaf00652_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00652=true := by decide +kernel
#print axioms leaf00652_sign
theorem leaf00652_log : RationalLog.accepts (801673841/2147483648) (-2116023505/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00652_log
def leaf00652 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (336531918037/1000000000000) (801673841/2147483648) (-2116023505/4294967296) 2 8 ![60,0,4] ![(31/1280),0,(1/8)] ![(3/6400),1,(1/8)] affine00652
theorem leaf00652_checked : FastNestedCellData.accepts 1 2 4 leaf00652=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (336531918037/1000000000000) (801673841/2147483648) (-2116023505/4294967296) 2 8 ![60,0,4] ![(31/1280),0,(1/8)] ![(3/6400),1,(1/8)] 1551979541165784577744933224448000000000000 774342637891303537006358026437865024520192 2300948576907847533382458146816000000000000 raw00652 affine00652
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00652_raw leaf00652_rectangular
    leaf00652_transform leaf00652_sign leaf00652_log
#print axioms leaf00652_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
