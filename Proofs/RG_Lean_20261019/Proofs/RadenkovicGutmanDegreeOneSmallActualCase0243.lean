/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0243 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0243 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,4,5,6,7,2,3] (sourceLabel 5 0 0 v)
def fusedMap0243 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![5,0,1,2,3,4,6,7] (fusedLabel 5 0 0 v)
theorem sourceMap0243_checked : acceptsGraphIso
    (source (graph core0243) (root 5) 0 0) DegreeOneSmallSpectrum033.graph sourceMap0243=true := by decide +kernel
theorem fusedMap0243_checked : acceptsGraphIso
    (fused (graph core0243) (root 5) 0 0) DegreeOneSmallSpectrum023.graph fusedMap0243=true := by decide +kernel
theorem certified0243 : Certified (graph core0243) (root 5) 0 0 :=
  of_native_maps core0243 DegreeOneSmallSpectrum033.graph DegreeOneSmallSpectrum023.graph
    sourceMap0243 fusedMap0243 sourceMap0243_checked fusedMap0243_checked
    DegreeOneSmallComparisons.comparison0243
#print axioms sourceMap0243_checked
#print axioms fusedMap0243_checked
#print axioms certified0243
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
