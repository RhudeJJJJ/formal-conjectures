/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00783 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 49122919032623562202448868147200000000000 29158712831746285003755965795769576849408 109497424770053839052941452902400000000000))
theorem leaf00783_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 49122919032623562202448868147200000000000 29158712831746285003755965795769576849408 109497424770053839052941452902400000000000 raw00783=true := by decide +kernel
#print axioms leaf00783_raw
theorem leaf00783_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00783=true := by decide +kernel
#print axioms leaf00783_rectangular
def affine00783 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00783 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00783_transform : affine00783=(NestedInteger.clearedAll 3 raw00783 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00783_transform
theorem leaf00783_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00783=true := by decide +kernel
#print axioms leaf00783_sign
theorem leaf00783_log : RationalLog.accepts (2013301657/4294967296) (-1627079607/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00783_log
def leaf00783 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (26629587767/100000000000) (2013301657/4294967296) (-1627079607/4294967296) 2 8 ![60,0,4] ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)] affine00783
theorem leaf00783_checked : FastNestedCellData.accepts 1 2 4 leaf00783=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (26629587767/100000000000) (2013301657/4294967296) (-1627079607/4294967296) 2 8 ![60,0,4] ![(31/800),0,(1/4)] ![(3/3200),1,(1/4)] 49122919032623562202448868147200000000000 29158712831746285003755965795769576849408 109497424770053839052941452902400000000000 raw00783 affine00783
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00783_raw leaf00783_rectangular
    leaf00783_transform leaf00783_sign leaf00783_log
#print axioms leaf00783_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
