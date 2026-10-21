/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1772 : Family 10 := level10.get ⟨5,by decide⟩
def sourceMap1772 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,7,8,9,10,11,12,5,6] (sourceLabel 10 0 0 v)
def fusedMap1772 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1772_checked : acceptsGraphIso
    (source (graph core1772) (root 10) 0 0) DegreeOneSmallSpectrum908.graph sourceMap1772=true := by decide +kernel
theorem fusedMap1772_checked : acceptsGraphIso
    (fused (graph core1772) (root 10) 0 0) DegreeOneSmallSpectrum860.graph fusedMap1772=true := by decide +kernel
theorem certified1772 : Certified (graph core1772) (root 10) 0 0 :=
  of_native_maps core1772 DegreeOneSmallSpectrum908.graph DegreeOneSmallSpectrum860.graph
    sourceMap1772 fusedMap1772 sourceMap1772_checked fusedMap1772_checked
    DegreeOneSmallComparisons.comparison1772
#print axioms sourceMap1772_checked
#print axioms fusedMap1772_checked
#print axioms certified1772
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
