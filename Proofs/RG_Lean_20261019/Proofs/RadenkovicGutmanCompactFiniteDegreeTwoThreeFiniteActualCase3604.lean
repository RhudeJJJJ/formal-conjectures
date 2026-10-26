/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3604 : Family 8 := level8.get ⟨198,by decide⟩
def sourceMap3604 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3604 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3604_checked : acceptsGraphIso
    (source (graph core3604) (root 8) 0 6) DegreeTwoThreeSpectrum6066.graph sourceMap3604=true := by decide +kernel
theorem fusedMap3604_checked : acceptsGraphIso
    (fused (graph core3604) (root 8) 0 6) DegreeTwoThreeSpectrum5161.graph fusedMap3604=true := by decide +kernel
theorem certified3604 : Certified (graph core3604) (root 8) 0 6 :=
  of_native_maps core3604 DegreeTwoThreeSpectrum6066.graph DegreeTwoThreeSpectrum5161.graph
    sourceMap3604 fusedMap3604 sourceMap3604_checked fusedMap3604_checked
    DegreeTwoThreeFiniteComparisons.comparison3604
#print axioms sourceMap3604_checked
#print axioms fusedMap3604_checked
#print axioms certified3604
def sourceMap3604swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3604swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3604swap_checked : acceptsGraphIso
    (source (graph core3604) (root 8) 6 0) DegreeTwoThreeSpectrum6066.graph sourceMap3604swap=true := by decide +kernel
theorem fusedMap3604swap_checked : acceptsGraphIso
    (fused (graph core3604) (root 8) 6 0) DegreeTwoThreeSpectrum5161.graph fusedMap3604swap=true := by decide +kernel
theorem certified3604swap : Certified (graph core3604) (root 8) 6 0 :=
  of_native_maps core3604 DegreeTwoThreeSpectrum6066.graph DegreeTwoThreeSpectrum5161.graph
    sourceMap3604swap fusedMap3604swap sourceMap3604swap_checked fusedMap3604swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3604
#print axioms sourceMap3604swap_checked
#print axioms fusedMap3604swap_checked
#print axioms certified3604swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
