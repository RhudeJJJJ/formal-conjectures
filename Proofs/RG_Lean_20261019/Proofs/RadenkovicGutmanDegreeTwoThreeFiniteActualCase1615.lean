/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1615 : Family 10 := level10.get ⟨647,by decide⟩
def sourceMap1615 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,13,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1615 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1615_checked : acceptsGraphIso
    (source (graph core1615) (root 10) 0 2) DegreeTwoThreeSpectrum3341.graph sourceMap1615=true := by decide +kernel
theorem fusedMap1615_checked : acceptsGraphIso
    (fused (graph core1615) (root 10) 0 2) DegreeTwoThreeSpectrum2592.graph fusedMap1615=true := by decide +kernel
theorem certified1615 : Certified (graph core1615) (root 10) 0 2 :=
  of_native_maps core1615 DegreeTwoThreeSpectrum3341.graph DegreeTwoThreeSpectrum2592.graph
    sourceMap1615 fusedMap1615 sourceMap1615_checked fusedMap1615_checked
    DegreeTwoThreeFiniteComparisons.comparison1615
#print axioms sourceMap1615_checked
#print axioms fusedMap1615_checked
#print axioms certified1615
def sourceMap1615swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,8,9,10,13] (sourceLabel 10 2 0 v)
def fusedMap1615swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1615swap_checked : acceptsGraphIso
    (source (graph core1615) (root 10) 2 0) DegreeTwoThreeSpectrum3341.graph sourceMap1615swap=true := by decide +kernel
theorem fusedMap1615swap_checked : acceptsGraphIso
    (fused (graph core1615) (root 10) 2 0) DegreeTwoThreeSpectrum2592.graph fusedMap1615swap=true := by decide +kernel
theorem certified1615swap : Certified (graph core1615) (root 10) 2 0 :=
  of_native_maps core1615 DegreeTwoThreeSpectrum3341.graph DegreeTwoThreeSpectrum2592.graph
    sourceMap1615swap fusedMap1615swap sourceMap1615swap_checked fusedMap1615swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1615
#print axioms sourceMap1615swap_checked
#print axioms fusedMap1615swap_checked
#print axioms certified1615swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
