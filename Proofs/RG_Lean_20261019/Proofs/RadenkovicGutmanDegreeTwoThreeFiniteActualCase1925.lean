/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1925 : Family 10 := level10.get ⟨1432,by decide⟩
def sourceMap1925 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,1,2,3,7,4,5,6] (sourceLabel 10 0 2 v)
def fusedMap1925 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1925_checked : acceptsGraphIso
    (source (graph core1925) (root 10) 0 2) DegreeTwoThreeSpectrum3622.graph sourceMap1925=true := by decide +kernel
theorem fusedMap1925_checked : acceptsGraphIso
    (fused (graph core1925) (root 10) 0 2) DegreeTwoThreeSpectrum3664.graph fusedMap1925=true := by decide +kernel
theorem certified1925 : Certified (graph core1925) (root 10) 0 2 :=
  of_native_maps core1925 DegreeTwoThreeSpectrum3622.graph DegreeTwoThreeSpectrum3664.graph
    sourceMap1925 fusedMap1925 sourceMap1925_checked fusedMap1925_checked
    DegreeTwoThreeFiniteComparisons.comparison1925
#print axioms sourceMap1925_checked
#print axioms fusedMap1925_checked
#print axioms certified1925
def sourceMap1925swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,1,2,3,4,5,6,7] (sourceLabel 10 2 0 v)
def fusedMap1925swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1925swap_checked : acceptsGraphIso
    (source (graph core1925) (root 10) 2 0) DegreeTwoThreeSpectrum3622.graph sourceMap1925swap=true := by decide +kernel
theorem fusedMap1925swap_checked : acceptsGraphIso
    (fused (graph core1925) (root 10) 2 0) DegreeTwoThreeSpectrum3664.graph fusedMap1925swap=true := by decide +kernel
theorem certified1925swap : Certified (graph core1925) (root 10) 2 0 :=
  of_native_maps core1925 DegreeTwoThreeSpectrum3622.graph DegreeTwoThreeSpectrum3664.graph
    sourceMap1925swap fusedMap1925swap sourceMap1925swap_checked fusedMap1925swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1925
#print axioms sourceMap1925swap_checked
#print axioms fusedMap1925swap_checked
#print axioms certified1925swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
