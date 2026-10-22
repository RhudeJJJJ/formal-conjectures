/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3586 : Family 8 := level8.get ⟨155,by decide⟩
def sourceMap3586 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3586 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3586_checked : acceptsGraphIso
    (source (graph core3586) (root 8) 0 6) DegreeTwoThreeSpectrum5575.graph sourceMap3586=true := by decide +kernel
theorem fusedMap3586_checked : acceptsGraphIso
    (fused (graph core3586) (root 8) 0 6) DegreeTwoThreeSpectrum5577.graph fusedMap3586=true := by decide +kernel
theorem certified3586 : Certified (graph core3586) (root 8) 0 6 :=
  of_native_maps core3586 DegreeTwoThreeSpectrum5575.graph DegreeTwoThreeSpectrum5577.graph
    sourceMap3586 fusedMap3586 sourceMap3586_checked fusedMap3586_checked
    DegreeTwoThreeFiniteComparisons.comparison3586
#print axioms sourceMap3586_checked
#print axioms fusedMap3586_checked
#print axioms certified3586
def sourceMap3586swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3586swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3586swap_checked : acceptsGraphIso
    (source (graph core3586) (root 8) 6 0) DegreeTwoThreeSpectrum5575.graph sourceMap3586swap=true := by decide +kernel
theorem fusedMap3586swap_checked : acceptsGraphIso
    (fused (graph core3586) (root 8) 6 0) DegreeTwoThreeSpectrum5577.graph fusedMap3586swap=true := by decide +kernel
theorem certified3586swap : Certified (graph core3586) (root 8) 6 0 :=
  of_native_maps core3586 DegreeTwoThreeSpectrum5575.graph DegreeTwoThreeSpectrum5577.graph
    sourceMap3586swap fusedMap3586swap sourceMap3586swap_checked fusedMap3586swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3586
#print axioms sourceMap3586swap_checked
#print axioms fusedMap3586swap_checked
#print axioms certified3586swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
