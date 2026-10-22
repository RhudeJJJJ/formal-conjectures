/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1476 : Family 10 := level10.get ⟨205,by decide⟩
def sourceMap1476 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1476 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1476_checked : acceptsGraphIso
    (source (graph core1476) (root 10) 0 2) DegreeTwoThreeSpectrum2483.graph sourceMap1476=true := by decide +kernel
theorem fusedMap1476_checked : acceptsGraphIso
    (fused (graph core1476) (root 10) 0 2) DegreeTwoThreeSpectrum2485.graph fusedMap1476=true := by decide +kernel
theorem certified1476 : Certified (graph core1476) (root 10) 0 2 :=
  of_native_maps core1476 DegreeTwoThreeSpectrum2483.graph DegreeTwoThreeSpectrum2485.graph
    sourceMap1476 fusedMap1476 sourceMap1476_checked fusedMap1476_checked
    DegreeTwoThreeFiniteComparisons.comparison1476
#print axioms sourceMap1476_checked
#print axioms fusedMap1476_checked
#print axioms certified1476
def sourceMap1476swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1476swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1476swap_checked : acceptsGraphIso
    (source (graph core1476) (root 10) 2 0) DegreeTwoThreeSpectrum2483.graph sourceMap1476swap=true := by decide +kernel
theorem fusedMap1476swap_checked : acceptsGraphIso
    (fused (graph core1476) (root 10) 2 0) DegreeTwoThreeSpectrum2485.graph fusedMap1476swap=true := by decide +kernel
theorem certified1476swap : Certified (graph core1476) (root 10) 2 0 :=
  of_native_maps core1476 DegreeTwoThreeSpectrum2483.graph DegreeTwoThreeSpectrum2485.graph
    sourceMap1476swap fusedMap1476swap sourceMap1476swap_checked fusedMap1476swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1476
#print axioms sourceMap1476swap_checked
#print axioms fusedMap1476swap_checked
#print axioms certified1476swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
