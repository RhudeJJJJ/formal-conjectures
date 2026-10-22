/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00215 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18972589074271586941480311193600000000000 8948107676954412166011694993306025984 22597666452375520101269504000000000000))
theorem leaf00215_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18972589074271586941480311193600000000000 8948107676954412166011694993306025984 22597666452375520101269504000000000000 raw00215=true := by decide +kernel
#print axioms leaf00215_raw
theorem leaf00215_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00215=true := by decide +kernel
#print axioms leaf00215_rectangular
def affine00215 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00215 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/6400),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00215_transform : affine00215=(NestedInteger.clearedAll 3 raw00215 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/6400),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00215_transform
theorem leaf00215_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00215=true := by decide +kernel
#print axioms leaf00215_sign
theorem leaf00215_log : RationalLog.accepts (1451065/4294967296) (-4291156397/1073741824) 12 8=true := by decide +kernel
#print axioms leaf00215_log
def leaf00215 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (395974854121/1000000000000) (1451065/4294967296) (-4291156397/1073741824) 12 8 ![60,0,4] ![(29/6400),0,0] ![(3/32000),1,(1/16)] affine00215
theorem leaf00215_checked : FastNestedCellData.accepts 1 2 4 leaf00215=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (395974854121/1000000000000) (1451065/4294967296) (-4291156397/1073741824) 12 8 ![60,0,4] ![(29/6400),0,0] ![(3/32000),1,(1/16)] 18972589074271586941480311193600000000000 8948107676954412166011694993306025984 22597666452375520101269504000000000000 raw00215 affine00215
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00215_raw leaf00215_rectangular
    leaf00215_transform leaf00215_sign leaf00215_log
#print axioms leaf00215_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
