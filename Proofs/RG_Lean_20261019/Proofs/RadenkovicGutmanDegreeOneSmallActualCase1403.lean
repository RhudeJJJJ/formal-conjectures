/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1403 : Family 9 := level9.get ⟨148,by decide⟩
def sourceMap1403 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1403 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1403_checked : acceptsGraphIso
    (source (graph core1403) (root 9) 0 0) DegreeOneSmallSpectrum665.graph sourceMap1403=true := by decide +kernel
theorem fusedMap1403_checked : acceptsGraphIso
    (fused (graph core1403) (root 9) 0 0) DegreeOneSmallSpectrum413.graph fusedMap1403=true := by decide +kernel
theorem certified1403 : Certified (graph core1403) (root 9) 0 0 :=
  of_native_maps core1403 DegreeOneSmallSpectrum665.graph DegreeOneSmallSpectrum413.graph
    sourceMap1403 fusedMap1403 sourceMap1403_checked fusedMap1403_checked
    DegreeOneSmallComparisons.comparison1403
#print axioms sourceMap1403_checked
#print axioms fusedMap1403_checked
#print axioms certified1403
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
