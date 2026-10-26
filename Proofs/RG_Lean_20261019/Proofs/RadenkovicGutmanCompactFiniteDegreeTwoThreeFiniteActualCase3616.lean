/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3616 : Family 8 := level8.get ⟨222,by decide⟩
def sourceMap3616 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3616 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3616_checked : acceptsGraphIso
    (source (graph core3616) (root 8) 0 6) DegreeTwoThreeSpectrum6335.graph sourceMap3616=true := by decide +kernel
theorem fusedMap3616_checked : acceptsGraphIso
    (fused (graph core3616) (root 8) 0 6) DegreeTwoThreeSpectrum5305.graph fusedMap3616=true := by decide +kernel
theorem certified3616 : Certified (graph core3616) (root 8) 0 6 :=
  of_native_maps core3616 DegreeTwoThreeSpectrum6335.graph DegreeTwoThreeSpectrum5305.graph
    sourceMap3616 fusedMap3616 sourceMap3616_checked fusedMap3616_checked
    DegreeTwoThreeFiniteComparisons.comparison3616
#print axioms sourceMap3616_checked
#print axioms fusedMap3616_checked
#print axioms certified3616
def sourceMap3616swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3616swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3616swap_checked : acceptsGraphIso
    (source (graph core3616) (root 8) 6 0) DegreeTwoThreeSpectrum6335.graph sourceMap3616swap=true := by decide +kernel
theorem fusedMap3616swap_checked : acceptsGraphIso
    (fused (graph core3616) (root 8) 6 0) DegreeTwoThreeSpectrum5305.graph fusedMap3616swap=true := by decide +kernel
theorem certified3616swap : Certified (graph core3616) (root 8) 6 0 :=
  of_native_maps core3616 DegreeTwoThreeSpectrum6335.graph DegreeTwoThreeSpectrum5305.graph
    sourceMap3616swap fusedMap3616swap sourceMap3616swap_checked fusedMap3616swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3616
#print axioms sourceMap3616swap_checked
#print axioms fusedMap3616swap_checked
#print axioms certified3616swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
