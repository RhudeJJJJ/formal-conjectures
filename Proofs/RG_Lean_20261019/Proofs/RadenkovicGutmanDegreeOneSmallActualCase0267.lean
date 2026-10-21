/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0267 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0267 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![2,1,0,5,6,7,8,3,4] (sourceLabel 6 0 0 v)
def fusedMap0267 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![2,1,0,5,6,7,8,3,4] (fusedLabel 6 0 0 v)
theorem sourceMap0267_checked : acceptsGraphIso
    (source (graph core0267) (root 6) 0 0) DegreeOneSmallSpectrum034.graph sourceMap0267=true := by decide +kernel
theorem fusedMap0267_checked : acceptsGraphIso
    (fused (graph core0267) (root 6) 0 0) DegreeOneSmallSpectrum037.graph fusedMap0267=true := by decide +kernel
theorem certified0267 : Certified (graph core0267) (root 6) 0 0 :=
  of_native_maps core0267 DegreeOneSmallSpectrum034.graph DegreeOneSmallSpectrum037.graph
    sourceMap0267 fusedMap0267 sourceMap0267_checked fusedMap0267_checked
    DegreeOneSmallComparisons.comparison0267
#print axioms sourceMap0267_checked
#print axioms fusedMap0267_checked
#print axioms certified0267
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
