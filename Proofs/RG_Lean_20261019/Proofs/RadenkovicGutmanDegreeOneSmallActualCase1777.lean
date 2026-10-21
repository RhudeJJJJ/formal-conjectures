/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1777 : Family 10 := level10.get ⟨11,by decide⟩
def sourceMap1777 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (sourceLabel 10 0 0 v)
def fusedMap1777 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1777_checked : acceptsGraphIso
    (source (graph core1777) (root 10) 0 0) DegreeOneSmallSpectrum875.graph sourceMap1777=true := by decide +kernel
theorem fusedMap1777_checked : acceptsGraphIso
    (fused (graph core1777) (root 10) 0 0) DegreeOneSmallSpectrum879.graph fusedMap1777=true := by decide +kernel
theorem certified1777 : Certified (graph core1777) (root 10) 0 0 :=
  of_native_maps core1777 DegreeOneSmallSpectrum875.graph DegreeOneSmallSpectrum879.graph
    sourceMap1777 fusedMap1777 sourceMap1777_checked fusedMap1777_checked
    DegreeOneSmallComparisons.comparison1777
#print axioms sourceMap1777_checked
#print axioms fusedMap1777_checked
#print axioms certified1777
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
