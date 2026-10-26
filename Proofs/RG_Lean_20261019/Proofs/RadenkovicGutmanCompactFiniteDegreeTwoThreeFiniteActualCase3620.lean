/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3620 : Family 8 := level8.get ⟨233,by decide⟩
def sourceMap3620 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3620 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3620_checked : acceptsGraphIso
    (source (graph core3620) (root 8) 0 6) DegreeTwoThreeSpectrum6496.graph sourceMap3620=true := by decide +kernel
theorem fusedMap3620_checked : acceptsGraphIso
    (fused (graph core3620) (root 8) 0 6) DegreeTwoThreeSpectrum5424.graph fusedMap3620=true := by decide +kernel
theorem certified3620 : Certified (graph core3620) (root 8) 0 6 :=
  of_native_maps core3620 DegreeTwoThreeSpectrum6496.graph DegreeTwoThreeSpectrum5424.graph
    sourceMap3620 fusedMap3620 sourceMap3620_checked fusedMap3620_checked
    DegreeTwoThreeFiniteComparisons.comparison3620
#print axioms sourceMap3620_checked
#print axioms fusedMap3620_checked
#print axioms certified3620
def sourceMap3620swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3620swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3620swap_checked : acceptsGraphIso
    (source (graph core3620) (root 8) 6 0) DegreeTwoThreeSpectrum6496.graph sourceMap3620swap=true := by decide +kernel
theorem fusedMap3620swap_checked : acceptsGraphIso
    (fused (graph core3620) (root 8) 6 0) DegreeTwoThreeSpectrum5424.graph fusedMap3620swap=true := by decide +kernel
theorem certified3620swap : Certified (graph core3620) (root 8) 6 0 :=
  of_native_maps core3620 DegreeTwoThreeSpectrum6496.graph DegreeTwoThreeSpectrum5424.graph
    sourceMap3620swap fusedMap3620swap sourceMap3620swap_checked fusedMap3620swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3620
#print axioms sourceMap3620swap_checked
#print axioms fusedMap3620swap_checked
#print axioms certified3620swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
