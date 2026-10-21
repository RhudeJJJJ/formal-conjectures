/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0159 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0159 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![2,1,0,5,6,7,3,4] (sourceLabel 5 0 0 v)
def fusedMap0159 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![1,0,4,5,6,7,2,3] (fusedLabel 5 0 0 v)
theorem sourceMap0159_checked : acceptsGraphIso
    (source (graph core0159) (root 5) 0 0) DegreeOneSmallSpectrum021.graph sourceMap0159=true := by decide +kernel
theorem fusedMap0159_checked : acceptsGraphIso
    (fused (graph core0159) (root 5) 0 0) DegreeOneSmallSpectrum016.graph fusedMap0159=true := by decide +kernel
theorem certified0159 : Certified (graph core0159) (root 5) 0 0 :=
  of_native_maps core0159 DegreeOneSmallSpectrum021.graph DegreeOneSmallSpectrum016.graph
    sourceMap0159 fusedMap0159 sourceMap0159_checked fusedMap0159_checked
    DegreeOneSmallComparisons.comparison0159
#print axioms sourceMap0159_checked
#print axioms fusedMap0159_checked
#print axioms certified0159
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
