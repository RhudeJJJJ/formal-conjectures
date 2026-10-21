/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0375 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0375 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,6,7,8,4,5,2,3] (sourceLabel 6 0 0 v)
def fusedMap0375 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,4,5,6,7,8,2,3] (fusedLabel 6 0 0 v)
theorem sourceMap0375_checked : acceptsGraphIso
    (source (graph core0375) (root 6) 0 0) DegreeOneSmallSpectrum044.graph sourceMap0375=true := by decide +kernel
theorem fusedMap0375_checked : acceptsGraphIso
    (fused (graph core0375) (root 6) 0 0) DegreeOneSmallSpectrum062.graph fusedMap0375=true := by decide +kernel
theorem certified0375 : Certified (graph core0375) (root 6) 0 0 :=
  of_native_maps core0375 DegreeOneSmallSpectrum044.graph DegreeOneSmallSpectrum062.graph
    sourceMap0375 fusedMap0375 sourceMap0375_checked fusedMap0375_checked
    DegreeOneSmallComparisons.comparison0375
#print axioms sourceMap0375_checked
#print axioms fusedMap0375_checked
#print axioms certified0375
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
