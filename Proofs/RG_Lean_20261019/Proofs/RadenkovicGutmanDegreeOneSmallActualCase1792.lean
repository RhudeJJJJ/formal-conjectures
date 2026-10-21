/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1792 : Family 10 := level10.get ⟨28,by decide⟩
def sourceMap1792 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1792 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1792_checked : acceptsGraphIso
    (source (graph core1792) (root 10) 0 0) DegreeOneSmallSpectrum903.graph sourceMap1792=true := by decide +kernel
theorem fusedMap1792_checked : acceptsGraphIso
    (fused (graph core1792) (root 10) 0 0) DegreeOneSmallSpectrum961.graph fusedMap1792=true := by decide +kernel
theorem certified1792 : Certified (graph core1792) (root 10) 0 0 :=
  of_native_maps core1792 DegreeOneSmallSpectrum903.graph DegreeOneSmallSpectrum961.graph
    sourceMap1792 fusedMap1792 sourceMap1792_checked fusedMap1792_checked
    DegreeOneSmallComparisons.comparison1792
#print axioms sourceMap1792_checked
#print axioms fusedMap1792_checked
#print axioms certified1792
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
