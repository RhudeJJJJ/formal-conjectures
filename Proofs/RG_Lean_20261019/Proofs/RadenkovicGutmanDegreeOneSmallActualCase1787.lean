/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1787 : Family 10 := level10.get ⟨22,by decide⟩
def sourceMap1787 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1787 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1787_checked : acceptsGraphIso
    (source (graph core1787) (root 10) 0 0) DegreeOneSmallSpectrum891.graph sourceMap1787=true := by decide +kernel
theorem fusedMap1787_checked : acceptsGraphIso
    (fused (graph core1787) (root 10) 0 0) DegreeOneSmallSpectrum944.graph fusedMap1787=true := by decide +kernel
theorem certified1787 : Certified (graph core1787) (root 10) 0 0 :=
  of_native_maps core1787 DegreeOneSmallSpectrum891.graph DegreeOneSmallSpectrum944.graph
    sourceMap1787 fusedMap1787 sourceMap1787_checked fusedMap1787_checked
    DegreeOneSmallComparisons.comparison1787
#print axioms sourceMap1787_checked
#print axioms fusedMap1787_checked
#print axioms certified1787
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
