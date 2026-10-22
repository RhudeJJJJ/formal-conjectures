/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1868 : Family 10 := level10.get ⟨1299,by decide⟩
def sourceMap1868 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1868 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1868_checked : acceptsGraphIso
    (source (graph core1868) (root 10) 0 2) DegreeTwoThreeSpectrum3461.graph sourceMap1868=true := by decide +kernel
theorem fusedMap1868_checked : acceptsGraphIso
    (fused (graph core1868) (root 10) 0 2) DegreeTwoThreeSpectrum3462.graph fusedMap1868=true := by decide +kernel
theorem certified1868 : Certified (graph core1868) (root 10) 0 2 :=
  of_native_maps core1868 DegreeTwoThreeSpectrum3461.graph DegreeTwoThreeSpectrum3462.graph
    sourceMap1868 fusedMap1868 sourceMap1868_checked fusedMap1868_checked
    DegreeTwoThreeFiniteComparisons.comparison1868
#print axioms sourceMap1868_checked
#print axioms fusedMap1868_checked
#print axioms certified1868
def sourceMap1868swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1868swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1868swap_checked : acceptsGraphIso
    (source (graph core1868) (root 10) 2 0) DegreeTwoThreeSpectrum3461.graph sourceMap1868swap=true := by decide +kernel
theorem fusedMap1868swap_checked : acceptsGraphIso
    (fused (graph core1868) (root 10) 2 0) DegreeTwoThreeSpectrum3462.graph fusedMap1868swap=true := by decide +kernel
theorem certified1868swap : Certified (graph core1868) (root 10) 2 0 :=
  of_native_maps core1868 DegreeTwoThreeSpectrum3461.graph DegreeTwoThreeSpectrum3462.graph
    sourceMap1868swap fusedMap1868swap sourceMap1868swap_checked fusedMap1868swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1868
#print axioms sourceMap1868swap_checked
#print axioms fusedMap1868swap_checked
#print axioms certified1868swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
