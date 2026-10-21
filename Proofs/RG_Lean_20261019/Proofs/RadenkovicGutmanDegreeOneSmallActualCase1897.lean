/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1897 : Family 10 := level10.get ⟨170,by decide⟩
def sourceMap1897 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,7,8,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1897 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1897_checked : acceptsGraphIso
    (source (graph core1897) (root 10) 0 0) DegreeOneSmallSpectrum1147.graph sourceMap1897=true := by decide +kernel
theorem fusedMap1897_checked : acceptsGraphIso
    (fused (graph core1897) (root 10) 0 0) DegreeOneSmallSpectrum958.graph fusedMap1897=true := by decide +kernel
theorem certified1897 : Certified (graph core1897) (root 10) 0 0 :=
  of_native_maps core1897 DegreeOneSmallSpectrum1147.graph DegreeOneSmallSpectrum958.graph
    sourceMap1897 fusedMap1897 sourceMap1897_checked fusedMap1897_checked
    DegreeOneSmallComparisons.comparison1897
#print axioms sourceMap1897_checked
#print axioms fusedMap1897_checked
#print axioms certified1897
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
