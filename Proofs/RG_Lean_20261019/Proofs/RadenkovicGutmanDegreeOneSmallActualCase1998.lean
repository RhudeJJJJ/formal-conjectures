/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1998 : Family 10 := level10.get ⟨329,by decide⟩
def sourceMap1998 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1998 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1998_checked : acceptsGraphIso
    (source (graph core1998) (root 10) 0 0) DegreeOneSmallSpectrum1269.graph sourceMap1998=true := by decide +kernel
theorem fusedMap1998_checked : acceptsGraphIso
    (fused (graph core1998) (root 10) 0 0) DegreeOneSmallSpectrum1418.graph fusedMap1998=true := by decide +kernel
theorem certified1998 : Certified (graph core1998) (root 10) 0 0 :=
  of_native_maps core1998 DegreeOneSmallSpectrum1269.graph DegreeOneSmallSpectrum1418.graph
    sourceMap1998 fusedMap1998 sourceMap1998_checked fusedMap1998_checked
    DegreeOneSmallComparisons.comparison1998
#print axioms sourceMap1998_checked
#print axioms fusedMap1998_checked
#print axioms certified1998
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
