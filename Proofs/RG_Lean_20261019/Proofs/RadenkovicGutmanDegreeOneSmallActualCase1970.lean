/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1970 : Family 10 := level10.get ⟨288,by decide⟩
def sourceMap1970 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1970 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1970_checked : acceptsGraphIso
    (source (graph core1970) (root 10) 0 0) DegreeOneSmallSpectrum1164.graph sourceMap1970=true := by decide +kernel
theorem fusedMap1970_checked : acceptsGraphIso
    (fused (graph core1970) (root 10) 0 0) DegreeOneSmallSpectrum1312.graph fusedMap1970=true := by decide +kernel
theorem certified1970 : Certified (graph core1970) (root 10) 0 0 :=
  of_native_maps core1970 DegreeOneSmallSpectrum1164.graph DegreeOneSmallSpectrum1312.graph
    sourceMap1970 fusedMap1970 sourceMap1970_checked fusedMap1970_checked
    DegreeOneSmallComparisons.comparison1970
#print axioms sourceMap1970_checked
#print axioms fusedMap1970_checked
#print axioms certified1970
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
