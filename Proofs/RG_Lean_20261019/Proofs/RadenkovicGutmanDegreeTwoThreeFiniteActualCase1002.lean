/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1002 : Family 10 := level10.get ⟨1719,by decide⟩
def sourceMap1002 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap1002 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap1002_checked : acceptsGraphIso
    (source (graph core1002) (root 10) 0 0) DegreeTwoThreeSpectrum1411.graph sourceMap1002=true := by decide +kernel
theorem fusedMap1002_checked : acceptsGraphIso
    (fused (graph core1002) (root 10) 0 0) DegreeTwoThreeSpectrum1387.graph fusedMap1002=true := by decide +kernel
theorem certified1002 : Certified (graph core1002) (root 10) 0 0 :=
  of_native_maps core1002 DegreeTwoThreeSpectrum1411.graph DegreeTwoThreeSpectrum1387.graph
    sourceMap1002 fusedMap1002 sourceMap1002_checked fusedMap1002_checked
    DegreeTwoThreeFiniteComparisons.comparison1002
#print axioms sourceMap1002_checked
#print axioms fusedMap1002_checked
#print axioms certified1002
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
