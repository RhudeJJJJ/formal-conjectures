/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1904 : Family 10 := level10.get ⟨189,by decide⟩
def sourceMap1904 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1904 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1904_checked : acceptsGraphIso
    (source (graph core1904) (root 10) 0 0) DegreeOneSmallSpectrum982.graph sourceMap1904=true := by decide +kernel
theorem fusedMap1904_checked : acceptsGraphIso
    (fused (graph core1904) (root 10) 0 0) DegreeOneSmallSpectrum985.graph fusedMap1904=true := by decide +kernel
theorem certified1904 : Certified (graph core1904) (root 10) 0 0 :=
  of_native_maps core1904 DegreeOneSmallSpectrum982.graph DegreeOneSmallSpectrum985.graph
    sourceMap1904 fusedMap1904 sourceMap1904_checked fusedMap1904_checked
    DegreeOneSmallComparisons.comparison1904
#print axioms sourceMap1904_checked
#print axioms fusedMap1904_checked
#print axioms certified1904
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
