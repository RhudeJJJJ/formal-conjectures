/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4397 : Family 9 := level9.get ⟨591,by decide⟩
def sourceMap4397 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4397 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4397_checked : acceptsGraphIso
    (source (graph core4397) (root 9) 2 2) DegreeTwoThreeSpectrum4924.graph sourceMap4397=true := by decide +kernel
theorem fusedMap4397_checked : acceptsGraphIso
    (fused (graph core4397) (root 9) 2 2) DegreeTwoThreeSpectrum4267.graph fusedMap4397=true := by decide +kernel
theorem certified4397 : Certified (graph core4397) (root 9) 2 2 :=
  of_native_maps core4397 DegreeTwoThreeSpectrum4924.graph DegreeTwoThreeSpectrum4267.graph
    sourceMap4397 fusedMap4397 sourceMap4397_checked fusedMap4397_checked
    DegreeTwoThreeFiniteComparisons.comparison4397
#print axioms sourceMap4397_checked
#print axioms fusedMap4397_checked
#print axioms certified4397
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
