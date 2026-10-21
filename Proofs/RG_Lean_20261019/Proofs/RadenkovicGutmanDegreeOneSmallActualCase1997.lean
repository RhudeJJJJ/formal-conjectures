/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1997 : Family 10 := level10.get ⟨327,by decide⟩
def sourceMap1997 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1997 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1997_checked : acceptsGraphIso
    (source (graph core1997) (root 10) 0 0) DegreeOneSmallSpectrum1170.graph sourceMap1997=true := by decide +kernel
theorem fusedMap1997_checked : acceptsGraphIso
    (fused (graph core1997) (root 10) 0 0) DegreeOneSmallSpectrum1413.graph fusedMap1997=true := by decide +kernel
theorem certified1997 : Certified (graph core1997) (root 10) 0 0 :=
  of_native_maps core1997 DegreeOneSmallSpectrum1170.graph DegreeOneSmallSpectrum1413.graph
    sourceMap1997 fusedMap1997 sourceMap1997_checked fusedMap1997_checked
    DegreeOneSmallComparisons.comparison1997
#print axioms sourceMap1997_checked
#print axioms fusedMap1997_checked
#print axioms certified1997
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
