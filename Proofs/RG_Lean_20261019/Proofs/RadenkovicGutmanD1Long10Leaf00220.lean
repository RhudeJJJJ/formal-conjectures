/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00220 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 77259351976275363933670342656000000000000 45499000991682147565190496037486089732096 169742482106072151224750178304000000000000))
theorem leaf00220_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 77259351976275363933670342656000000000000 45499000991682147565190496037486089732096 169742482106072151224750178304000000000000 raw00220=true := by decide +kernel
#print axioms leaf00220_raw
theorem leaf00220_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00220=true := by decide +kernel
#print axioms leaf00220_rectangular
def affine00220 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00220 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00220_transform : affine00220=(NestedInteger.clearedAll 3 raw00220 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00220_transform
theorem leaf00220_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00220=true := by decide +kernel
#print axioms leaf00220_sign
theorem leaf00220_log : RationalLog.accepts (1994689189/4294967296) (-1647024891/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00220_log
def leaf00220 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (33505902903/125000000000) (1994689189/4294967296) (-1647024891/4294967296) 2 8 ![52,0,4] ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)] affine00220
theorem leaf00220_checked : FastNestedCellData.accepts 1 0 4 leaf00220=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (33505902903/125000000000) (1994689189/4294967296) (-1647024891/4294967296) 2 8 ![52,0,4] ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)] 77259351976275363933670342656000000000000 45499000991682147565190496037486089732096 169742482106072151224750178304000000000000 raw00220 affine00220
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00220_raw leaf00220_rectangular
    leaf00220_transform leaf00220_sign leaf00220_log
#print axioms leaf00220_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
