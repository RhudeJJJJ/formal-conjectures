/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1993 : Family 10 := level10.get ⟨323,by decide⟩
def sourceMap1993 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1993 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1993_checked : acceptsGraphIso
    (source (graph core1993) (root 10) 0 0) DegreeOneSmallSpectrum1265.graph sourceMap1993=true := by decide +kernel
theorem fusedMap1993_checked : acceptsGraphIso
    (fused (graph core1993) (root 10) 0 0) DegreeOneSmallSpectrum1398.graph fusedMap1993=true := by decide +kernel
theorem certified1993 : Certified (graph core1993) (root 10) 0 0 :=
  of_native_maps core1993 DegreeOneSmallSpectrum1265.graph DegreeOneSmallSpectrum1398.graph
    sourceMap1993 fusedMap1993 sourceMap1993_checked fusedMap1993_checked
    DegreeOneSmallComparisons.comparison1993
#print axioms sourceMap1993_checked
#print axioms fusedMap1993_checked
#print axioms certified1993
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
