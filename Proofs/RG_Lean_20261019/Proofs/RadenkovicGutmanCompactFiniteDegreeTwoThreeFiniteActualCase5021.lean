/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5021 : Family 10 := level10.get ⟨1669,by decide⟩
def sourceMap5021 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,12,13,14,15,16,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap5021 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5021_checked : acceptsGraphIso
    (source (graph core5021) (root 10) 2 2) DegreeTwoThreeSpectrum7622.graph sourceMap5021=true := by decide +kernel
theorem fusedMap5021_checked : acceptsGraphIso
    (fused (graph core5021) (root 10) 2 2) DegreeTwoThreeSpectrum6289.graph fusedMap5021=true := by decide +kernel
theorem certified5021 : Certified (graph core5021) (root 10) 2 2 :=
  of_native_maps core5021 DegreeTwoThreeSpectrum7622.graph DegreeTwoThreeSpectrum6289.graph
    sourceMap5021 fusedMap5021 sourceMap5021_checked fusedMap5021_checked
    DegreeTwoThreeFiniteComparisons.comparison5021
#print axioms sourceMap5021_checked
#print axioms fusedMap5021_checked
#print axioms certified5021
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
