/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1020 : Family 10 := level10.get ⟨1812,by decide⟩
def sourceMap1020 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1020 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1020_checked : acceptsGraphIso
    (source (graph core1020) (root 10) 0 0) DegreeTwoThreeSpectrum1691.graph sourceMap1020=true := by decide +kernel
theorem fusedMap1020_checked : acceptsGraphIso
    (fused (graph core1020) (root 10) 0 0) DegreeTwoThreeSpectrum1690.graph fusedMap1020=true := by decide +kernel
theorem certified1020 : Certified (graph core1020) (root 10) 0 0 :=
  of_native_maps core1020 DegreeTwoThreeSpectrum1691.graph DegreeTwoThreeSpectrum1690.graph
    sourceMap1020 fusedMap1020 sourceMap1020_checked fusedMap1020_checked
    DegreeTwoThreeFiniteComparisons.comparison1020
#print axioms sourceMap1020_checked
#print axioms fusedMap1020_checked
#print axioms certified1020
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
