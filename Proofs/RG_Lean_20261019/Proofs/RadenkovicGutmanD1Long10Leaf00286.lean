/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00286 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4534368361707214929807424880640000000000 2336090547373208772057711229624066768896 5939810826840938919088881664000000000000))
theorem leaf00286_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4534368361707214929807424880640000000000 2336090547373208772057711229624066768896 5939810826840938919088881664000000000000 raw00286=true := by decide +kernel
#print axioms leaf00286_raw
theorem leaf00286_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00286=true := by decide +kernel
#print axioms leaf00286_rectangular
def affine00286 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00286 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00286_transform : affine00286=(NestedInteger.clearedAll 3 raw00286 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00286_transform
theorem leaf00286_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00286=true := by decide +kernel
#print axioms leaf00286_sign
theorem leaf00286_log : RationalLog.accepts (198518075/536870912) (-1068241643/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00286_log
def leaf00286 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (393293762289/1000000000000) (198518075/536870912) (-1068241643/2147483648) 2 8 ![52,0,4] ![(43/640),0,(1/4)] ![(1/640),1,(1/4)] affine00286
theorem leaf00286_checked : FastNestedCellData.accepts 1 0 4 leaf00286=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (393293762289/1000000000000) (198518075/536870912) (-1068241643/2147483648) 2 8 ![52,0,4] ![(43/640),0,(1/4)] ![(1/640),1,(1/4)] 4534368361707214929807424880640000000000 2336090547373208772057711229624066768896 5939810826840938919088881664000000000000 raw00286 affine00286
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00286_raw leaf00286_rectangular
    leaf00286_transform leaf00286_sign leaf00286_log
#print axioms leaf00286_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
