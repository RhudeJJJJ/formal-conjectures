/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1019 : Family 10 := level10.get ⟨1807,by decide⟩
def sourceMap1019 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1019 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1019_checked : acceptsGraphIso
    (source (graph core1019) (root 10) 0 0) DegreeTwoThreeSpectrum1689.graph sourceMap1019=true := by decide +kernel
theorem fusedMap1019_checked : acceptsGraphIso
    (fused (graph core1019) (root 10) 0 0) DegreeTwoThreeSpectrum1688.graph fusedMap1019=true := by decide +kernel
theorem certified1019 : Certified (graph core1019) (root 10) 0 0 :=
  of_native_maps core1019 DegreeTwoThreeSpectrum1689.graph DegreeTwoThreeSpectrum1688.graph
    sourceMap1019 fusedMap1019 sourceMap1019_checked fusedMap1019_checked
    DegreeTwoThreeFiniteComparisons.comparison1019
#print axioms sourceMap1019_checked
#print axioms fusedMap1019_checked
#print axioms certified1019
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
