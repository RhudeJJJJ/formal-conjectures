/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1358 : Family 9 := level9.get ⟨107,by decide⟩
def sourceMap1358 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1358 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1358_checked : acceptsGraphIso
    (source (graph core1358) (root 9) 0 1) DegreeOneSmallSpectrum1413.graph sourceMap1358=true := by decide +kernel
theorem fusedMap1358_checked : acceptsGraphIso
    (fused (graph core1358) (root 9) 0 1) DegreeOneSmallSpectrum963.graph fusedMap1358=true := by decide +kernel
theorem certified1358 : Certified (graph core1358) (root 9) 0 1 :=
  of_native_maps core1358 DegreeOneSmallSpectrum1413.graph DegreeOneSmallSpectrum963.graph
    sourceMap1358 fusedMap1358 sourceMap1358_checked fusedMap1358_checked
    DegreeOneSmallComparisons.comparison1358
#print axioms sourceMap1358_checked
#print axioms fusedMap1358_checked
#print axioms certified1358
def sourceMap1358swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1358swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1358swap_checked : acceptsGraphIso
    (source (graph core1358) (root 9) 1 0) DegreeOneSmallSpectrum1413.graph sourceMap1358swap=true := by decide +kernel
theorem fusedMap1358swap_checked : acceptsGraphIso
    (fused (graph core1358) (root 9) 1 0) DegreeOneSmallSpectrum963.graph fusedMap1358swap=true := by decide +kernel
theorem certified1358swap : Certified (graph core1358) (root 9) 1 0 :=
  of_native_maps core1358 DegreeOneSmallSpectrum1413.graph DegreeOneSmallSpectrum963.graph
    sourceMap1358swap fusedMap1358swap sourceMap1358swap_checked fusedMap1358swap_checked
    DegreeOneSmallComparisons.comparison1358
#print axioms sourceMap1358swap_checked
#print axioms fusedMap1358swap_checked
#print axioms certified1358swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
