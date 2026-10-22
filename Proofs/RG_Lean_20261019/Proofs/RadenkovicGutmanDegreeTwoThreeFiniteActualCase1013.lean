/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1013 : Family 10 := level10.get ⟨1755,by decide⟩
def sourceMap1013 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap1013 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap1013_checked : acceptsGraphIso
    (source (graph core1013) (root 10) 0 0) DegreeTwoThreeSpectrum1325.graph sourceMap1013=true := by decide +kernel
theorem fusedMap1013_checked : acceptsGraphIso
    (fused (graph core1013) (root 10) 0 0) DegreeTwoThreeSpectrum1317.graph fusedMap1013=true := by decide +kernel
theorem certified1013 : Certified (graph core1013) (root 10) 0 0 :=
  of_native_maps core1013 DegreeTwoThreeSpectrum1325.graph DegreeTwoThreeSpectrum1317.graph
    sourceMap1013 fusedMap1013 sourceMap1013_checked fusedMap1013_checked
    DegreeTwoThreeFiniteComparisons.comparison1013
#print axioms sourceMap1013_checked
#print axioms fusedMap1013_checked
#print axioms certified1013
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
