/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00697 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1748202933466582028076898582528000000000000 811961100544882932992109862592996572135424 2141919329390788804799293816832000000000000))
theorem leaf00697_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1748202933466582028076898582528000000000000 811961100544882932992109862592996572135424 2141919329390788804799293816832000000000000 raw00697=true := by decide +kernel
#print axioms leaf00697_raw
theorem leaf00697_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00697=true := by decide +kernel
#print axioms leaf00697_rectangular
def affine00697 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00697 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00697_transform : affine00697=(NestedInteger.clearedAll 3 raw00697 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00697_transform
theorem leaf00697_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00697=true := by decide +kernel
#print axioms leaf00697_sign
theorem leaf00697_log : RationalLog.accepts (1446483349/4294967296) (-146070313/268435456) 2 8=true := by decide +kernel
#print axioms leaf00697_log
def leaf00697 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (189540541841/500000000000) (1446483349/4294967296) (-146070313/268435456) 2 8 ![60,0,4] ![(91/3200),0,(1/8)] ![(3/6400),1,(1/8)] affine00697
theorem leaf00697_checked : FastNestedCellData.accepts 1 2 4 leaf00697=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (189540541841/500000000000) (1446483349/4294967296) (-146070313/268435456) 2 8 ![60,0,4] ![(91/3200),0,(1/8)] ![(3/6400),1,(1/8)] 1748202933466582028076898582528000000000000 811961100544882932992109862592996572135424 2141919329390788804799293816832000000000000 raw00697 affine00697
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00697_raw leaf00697_rectangular
    leaf00697_transform leaf00697_sign leaf00697_log
#print axioms leaf00697_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
