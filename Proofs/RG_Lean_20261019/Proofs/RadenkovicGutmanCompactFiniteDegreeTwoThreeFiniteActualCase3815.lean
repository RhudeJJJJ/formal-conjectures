/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3815 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap3815 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3815 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3815_checked : acceptsGraphIso
    (source (graph core3815) (root 7) 1 4) DegreeTwoThreeSpectrum3288.graph sourceMap3815=true := by decide +kernel
theorem fusedMap3815_checked : acceptsGraphIso
    (fused (graph core3815) (root 7) 1 4) DegreeTwoThreeSpectrum2565.graph fusedMap3815=true := by decide +kernel
theorem certified3815 : Certified (graph core3815) (root 7) 1 4 :=
  of_native_maps core3815 DegreeTwoThreeSpectrum3288.graph DegreeTwoThreeSpectrum2565.graph
    sourceMap3815 fusedMap3815 sourceMap3815_checked fusedMap3815_checked
    DegreeTwoThreeFiniteComparisons.comparison3815
#print axioms sourceMap3815_checked
#print axioms fusedMap3815_checked
#print axioms certified3815
def sourceMap3815swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3815swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3815swap_checked : acceptsGraphIso
    (source (graph core3815) (root 7) 4 1) DegreeTwoThreeSpectrum3288.graph sourceMap3815swap=true := by decide +kernel
theorem fusedMap3815swap_checked : acceptsGraphIso
    (fused (graph core3815) (root 7) 4 1) DegreeTwoThreeSpectrum2565.graph fusedMap3815swap=true := by decide +kernel
theorem certified3815swap : Certified (graph core3815) (root 7) 4 1 :=
  of_native_maps core3815 DegreeTwoThreeSpectrum3288.graph DegreeTwoThreeSpectrum2565.graph
    sourceMap3815swap fusedMap3815swap sourceMap3815swap_checked fusedMap3815swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3815
#print axioms sourceMap3815swap_checked
#print axioms fusedMap3815swap_checked
#print axioms certified3815swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
