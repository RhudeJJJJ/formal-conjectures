/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1924 : Family 10 := level10.get ⟨216,by decide⟩
def sourceMap1924 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1924 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1924_checked : acceptsGraphIso
    (source (graph core1924) (root 10) 0 0) DegreeOneSmallSpectrum1092.graph sourceMap1924=true := by decide +kernel
theorem fusedMap1924_checked : acceptsGraphIso
    (fused (graph core1924) (root 10) 0 0) DegreeOneSmallSpectrum1095.graph fusedMap1924=true := by decide +kernel
theorem certified1924 : Certified (graph core1924) (root 10) 0 0 :=
  of_native_maps core1924 DegreeOneSmallSpectrum1092.graph DegreeOneSmallSpectrum1095.graph
    sourceMap1924 fusedMap1924 sourceMap1924_checked fusedMap1924_checked
    DegreeOneSmallComparisons.comparison1924
#print axioms sourceMap1924_checked
#print axioms fusedMap1924_checked
#print axioms certified1924
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
