/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1807 : Family 10 := level10.get ⟨46,by decide⟩
def sourceMap1807 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1807 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1807_checked : acceptsGraphIso
    (source (graph core1807) (root 10) 0 0) DegreeOneSmallSpectrum873.graph sourceMap1807=true := by decide +kernel
theorem fusedMap1807_checked : acceptsGraphIso
    (fused (graph core1807) (root 10) 0 0) DegreeOneSmallSpectrum961.graph fusedMap1807=true := by decide +kernel
theorem certified1807 : Certified (graph core1807) (root 10) 0 0 :=
  of_native_maps core1807 DegreeOneSmallSpectrum873.graph DegreeOneSmallSpectrum961.graph
    sourceMap1807 fusedMap1807 sourceMap1807_checked fusedMap1807_checked
    DegreeOneSmallComparisons.comparison1807
#print axioms sourceMap1807_checked
#print axioms fusedMap1807_checked
#print axioms certified1807
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
