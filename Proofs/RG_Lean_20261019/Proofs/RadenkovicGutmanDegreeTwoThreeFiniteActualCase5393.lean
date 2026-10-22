/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5393 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap5393 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5393 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5393_checked : acceptsGraphIso
    (source (graph core5393) (root 6) 4 4) DegreeTwoThreeSpectrum7052.graph sourceMap5393=true := by decide +kernel
theorem fusedMap5393_checked : acceptsGraphIso
    (fused (graph core5393) (root 6) 4 4) DegreeTwoThreeSpectrum5048.graph fusedMap5393=true := by decide +kernel
theorem certified5393 : Certified (graph core5393) (root 6) 4 4 :=
  of_native_maps core5393 DegreeTwoThreeSpectrum7052.graph DegreeTwoThreeSpectrum5048.graph
    sourceMap5393 fusedMap5393 sourceMap5393_checked fusedMap5393_checked
    DegreeTwoThreeFiniteComparisons.comparison5393
#print axioms sourceMap5393_checked
#print axioms fusedMap5393_checked
#print axioms certified5393
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
