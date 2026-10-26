/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3705 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3705 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (sourceLabel 5 0 8 v)
def fusedMap3705 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 0 8 v)
theorem sourceMap3705_checked : acceptsGraphIso
    (source (graph core3705) (root 5) 0 8) DegreeTwoThreeSpectrum3949.graph sourceMap3705=true := by decide +kernel
theorem fusedMap3705_checked : acceptsGraphIso
    (fused (graph core3705) (root 5) 0 8) DegreeTwoThreeSpectrum3856.graph fusedMap3705=true := by decide +kernel
theorem certified3705 : Certified (graph core3705) (root 5) 0 8 :=
  of_native_maps core3705 DegreeTwoThreeSpectrum3949.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap3705 fusedMap3705 sourceMap3705_checked fusedMap3705_checked
    DegreeTwoThreeFiniteComparisons.comparison3705
#print axioms sourceMap3705_checked
#print axioms fusedMap3705_checked
#print axioms certified3705
def sourceMap3705swap : (Vertices 5 ⊕ Fin 9 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,9] (sourceLabel 5 8 0 v)
def fusedMap3705swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 8 0 v)
theorem sourceMap3705swap_checked : acceptsGraphIso
    (source (graph core3705) (root 5) 8 0) DegreeTwoThreeSpectrum3949.graph sourceMap3705swap=true := by decide +kernel
theorem fusedMap3705swap_checked : acceptsGraphIso
    (fused (graph core3705) (root 5) 8 0) DegreeTwoThreeSpectrum3856.graph fusedMap3705swap=true := by decide +kernel
theorem certified3705swap : Certified (graph core3705) (root 5) 8 0 :=
  of_native_maps core3705 DegreeTwoThreeSpectrum3949.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap3705swap fusedMap3705swap sourceMap3705swap_checked fusedMap3705swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3705
#print axioms sourceMap3705swap_checked
#print axioms fusedMap3705swap_checked
#print axioms certified3705swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
