/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1838 : Family 10 := level10.get ⟨89,by decide⟩
def sourceMap1838 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1838 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1838_checked : acceptsGraphIso
    (source (graph core1838) (root 10) 0 0) DegreeOneSmallSpectrum1257.graph sourceMap1838=true := by decide +kernel
theorem fusedMap1838_checked : acceptsGraphIso
    (fused (graph core1838) (root 10) 0 0) DegreeOneSmallSpectrum911.graph fusedMap1838=true := by decide +kernel
theorem certified1838 : Certified (graph core1838) (root 10) 0 0 :=
  of_native_maps core1838 DegreeOneSmallSpectrum1257.graph DegreeOneSmallSpectrum911.graph
    sourceMap1838 fusedMap1838 sourceMap1838_checked fusedMap1838_checked
    DegreeOneSmallComparisons.comparison1838
#print axioms sourceMap1838_checked
#print axioms fusedMap1838_checked
#print axioms certified1838
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
