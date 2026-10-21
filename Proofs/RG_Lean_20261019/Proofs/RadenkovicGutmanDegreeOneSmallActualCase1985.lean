/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1985 : Family 10 := level10.get ⟨310,by decide⟩
def sourceMap1985 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1985 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1985_checked : acceptsGraphIso
    (source (graph core1985) (root 10) 0 0) DegreeOneSmallSpectrum1262.graph sourceMap1985=true := by decide +kernel
theorem fusedMap1985_checked : acceptsGraphIso
    (fused (graph core1985) (root 10) 0 0) DegreeOneSmallSpectrum1374.graph fusedMap1985=true := by decide +kernel
theorem certified1985 : Certified (graph core1985) (root 10) 0 0 :=
  of_native_maps core1985 DegreeOneSmallSpectrum1262.graph DegreeOneSmallSpectrum1374.graph
    sourceMap1985 fusedMap1985 sourceMap1985_checked fusedMap1985_checked
    DegreeOneSmallComparisons.comparison1985
#print axioms sourceMap1985_checked
#print axioms fusedMap1985_checked
#print axioms certified1985
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
