/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1988 : Family 10 := level10.get ⟨314,by decide⟩
def sourceMap1988 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1988 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1988_checked : acceptsGraphIso
    (source (graph core1988) (root 10) 0 0) DegreeOneSmallSpectrum1205.graph sourceMap1988=true := by decide +kernel
theorem fusedMap1988_checked : acceptsGraphIso
    (fused (graph core1988) (root 10) 0 0) DegreeOneSmallSpectrum1392.graph fusedMap1988=true := by decide +kernel
theorem certified1988 : Certified (graph core1988) (root 10) 0 0 :=
  of_native_maps core1988 DegreeOneSmallSpectrum1205.graph DegreeOneSmallSpectrum1392.graph
    sourceMap1988 fusedMap1988 sourceMap1988_checked fusedMap1988_checked
    DegreeOneSmallComparisons.comparison1988
#print axioms sourceMap1988_checked
#print axioms fusedMap1988_checked
#print axioms certified1988
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
