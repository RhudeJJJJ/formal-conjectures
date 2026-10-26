/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3859 : Family 8 := level8.get ⟨117,by decide⟩
def sourceMap3859 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3859 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3859_checked : acceptsGraphIso
    (source (graph core3859) (root 8) 1 4) DegreeTwoThreeSpectrum4316.graph sourceMap3859=true := by decide +kernel
theorem fusedMap3859_checked : acceptsGraphIso
    (fused (graph core3859) (root 8) 1 4) DegreeTwoThreeSpectrum3929.graph fusedMap3859=true := by decide +kernel
theorem certified3859 : Certified (graph core3859) (root 8) 1 4 :=
  of_native_maps core3859 DegreeTwoThreeSpectrum4316.graph DegreeTwoThreeSpectrum3929.graph
    sourceMap3859 fusedMap3859 sourceMap3859_checked fusedMap3859_checked
    DegreeTwoThreeFiniteComparisons.comparison3859
#print axioms sourceMap3859_checked
#print axioms fusedMap3859_checked
#print axioms certified3859
def sourceMap3859swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3859swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3859swap_checked : acceptsGraphIso
    (source (graph core3859) (root 8) 4 1) DegreeTwoThreeSpectrum4316.graph sourceMap3859swap=true := by decide +kernel
theorem fusedMap3859swap_checked : acceptsGraphIso
    (fused (graph core3859) (root 8) 4 1) DegreeTwoThreeSpectrum3929.graph fusedMap3859swap=true := by decide +kernel
theorem certified3859swap : Certified (graph core3859) (root 8) 4 1 :=
  of_native_maps core3859 DegreeTwoThreeSpectrum4316.graph DegreeTwoThreeSpectrum3929.graph
    sourceMap3859swap fusedMap3859swap sourceMap3859swap_checked fusedMap3859swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3859
#print axioms sourceMap3859swap_checked
#print axioms fusedMap3859swap_checked
#print axioms certified3859swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
