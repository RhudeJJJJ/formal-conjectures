/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1964 : Family 10 := level10.get ⟨274,by decide⟩
def sourceMap1964 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap1964 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1964_checked : acceptsGraphIso
    (source (graph core1964) (root 10) 0 0) DegreeOneSmallSpectrum1092.graph sourceMap1964=true := by decide +kernel
theorem fusedMap1964_checked : acceptsGraphIso
    (fused (graph core1964) (root 10) 0 0) DegreeOneSmallSpectrum1281.graph fusedMap1964=true := by decide +kernel
theorem certified1964 : Certified (graph core1964) (root 10) 0 0 :=
  of_native_maps core1964 DegreeOneSmallSpectrum1092.graph DegreeOneSmallSpectrum1281.graph
    sourceMap1964 fusedMap1964 sourceMap1964_checked fusedMap1964_checked
    DegreeOneSmallComparisons.comparison1964
#print axioms sourceMap1964_checked
#print axioms fusedMap1964_checked
#print axioms certified1964
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
