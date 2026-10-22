/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1860 : Family 10 := level10.get ⟨1281,by decide⟩
def sourceMap1860 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1860 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1860_checked : acceptsGraphIso
    (source (graph core1860) (root 10) 0 2) DegreeTwoThreeSpectrum3435.graph sourceMap1860=true := by decide +kernel
theorem fusedMap1860_checked : acceptsGraphIso
    (fused (graph core1860) (root 10) 0 2) DegreeTwoThreeSpectrum3436.graph fusedMap1860=true := by decide +kernel
theorem certified1860 : Certified (graph core1860) (root 10) 0 2 :=
  of_native_maps core1860 DegreeTwoThreeSpectrum3435.graph DegreeTwoThreeSpectrum3436.graph
    sourceMap1860 fusedMap1860 sourceMap1860_checked fusedMap1860_checked
    DegreeTwoThreeFiniteComparisons.comparison1860
#print axioms sourceMap1860_checked
#print axioms fusedMap1860_checked
#print axioms certified1860
def sourceMap1860swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1860swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1860swap_checked : acceptsGraphIso
    (source (graph core1860) (root 10) 2 0) DegreeTwoThreeSpectrum3435.graph sourceMap1860swap=true := by decide +kernel
theorem fusedMap1860swap_checked : acceptsGraphIso
    (fused (graph core1860) (root 10) 2 0) DegreeTwoThreeSpectrum3436.graph fusedMap1860swap=true := by decide +kernel
theorem certified1860swap : Certified (graph core1860) (root 10) 2 0 :=
  of_native_maps core1860 DegreeTwoThreeSpectrum3435.graph DegreeTwoThreeSpectrum3436.graph
    sourceMap1860swap fusedMap1860swap sourceMap1860swap_checked fusedMap1860swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1860
#print axioms sourceMap1860swap_checked
#print axioms fusedMap1860swap_checked
#print axioms certified1860swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
