/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3223 : Family 8 := level8.get ⟨236,by decide⟩
def sourceMap3223 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3223 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3223_checked : acceptsGraphIso
    (source (graph core3223) (root 8) 0 5) DegreeTwoThreeSpectrum4415.graph sourceMap3223=true := by decide +kernel
theorem fusedMap3223_checked : acceptsGraphIso
    (fused (graph core3223) (root 8) 0 5) DegreeTwoThreeSpectrum4416.graph fusedMap3223=true := by decide +kernel
theorem certified3223 : Certified (graph core3223) (root 8) 0 5 :=
  of_native_maps core3223 DegreeTwoThreeSpectrum4415.graph DegreeTwoThreeSpectrum4416.graph
    sourceMap3223 fusedMap3223 sourceMap3223_checked fusedMap3223_checked
    DegreeTwoThreeFiniteComparisons.comparison3223
#print axioms sourceMap3223_checked
#print axioms fusedMap3223_checked
#print axioms certified3223
def sourceMap3223swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3223swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3223swap_checked : acceptsGraphIso
    (source (graph core3223) (root 8) 5 0) DegreeTwoThreeSpectrum4415.graph sourceMap3223swap=true := by decide +kernel
theorem fusedMap3223swap_checked : acceptsGraphIso
    (fused (graph core3223) (root 8) 5 0) DegreeTwoThreeSpectrum4416.graph fusedMap3223swap=true := by decide +kernel
theorem certified3223swap : Certified (graph core3223) (root 8) 5 0 :=
  of_native_maps core3223 DegreeTwoThreeSpectrum4415.graph DegreeTwoThreeSpectrum4416.graph
    sourceMap3223swap fusedMap3223swap sourceMap3223swap_checked fusedMap3223swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3223
#print axioms sourceMap3223swap_checked
#print axioms fusedMap3223swap_checked
#print axioms certified3223swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
