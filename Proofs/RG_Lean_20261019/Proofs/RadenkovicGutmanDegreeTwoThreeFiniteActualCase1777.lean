/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1777 : Family 10 := level10.get ⟨1078,by decide⟩
def sourceMap1777 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1777 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1777_checked : acceptsGraphIso
    (source (graph core1777) (root 10) 0 2) DegreeTwoThreeSpectrum3132.graph sourceMap1777=true := by decide +kernel
theorem fusedMap1777_checked : acceptsGraphIso
    (fused (graph core1777) (root 10) 0 2) DegreeTwoThreeSpectrum3133.graph fusedMap1777=true := by decide +kernel
theorem certified1777 : Certified (graph core1777) (root 10) 0 2 :=
  of_native_maps core1777 DegreeTwoThreeSpectrum3132.graph DegreeTwoThreeSpectrum3133.graph
    sourceMap1777 fusedMap1777 sourceMap1777_checked fusedMap1777_checked
    DegreeTwoThreeFiniteComparisons.comparison1777
#print axioms sourceMap1777_checked
#print axioms fusedMap1777_checked
#print axioms certified1777
def sourceMap1777swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1777swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1777swap_checked : acceptsGraphIso
    (source (graph core1777) (root 10) 2 0) DegreeTwoThreeSpectrum3132.graph sourceMap1777swap=true := by decide +kernel
theorem fusedMap1777swap_checked : acceptsGraphIso
    (fused (graph core1777) (root 10) 2 0) DegreeTwoThreeSpectrum3133.graph fusedMap1777swap=true := by decide +kernel
theorem certified1777swap : Certified (graph core1777) (root 10) 2 0 :=
  of_native_maps core1777 DegreeTwoThreeSpectrum3132.graph DegreeTwoThreeSpectrum3133.graph
    sourceMap1777swap fusedMap1777swap sourceMap1777swap_checked fusedMap1777swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1777
#print axioms sourceMap1777swap_checked
#print axioms fusedMap1777swap_checked
#print axioms certified1777swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
