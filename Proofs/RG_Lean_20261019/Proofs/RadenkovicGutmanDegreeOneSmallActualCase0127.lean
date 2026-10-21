/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0127 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0127 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![1,0,4,5,6,2,3] (sourceLabel 4 0 0 v)
def fusedMap0127 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![4,0,1,2,3,5,6] (fusedLabel 4 0 0 v)
theorem sourceMap0127_checked : acceptsGraphIso
    (source (graph core0127) (root 4) 0 0) DegreeOneSmallSpectrum014.graph sourceMap0127=true := by decide +kernel
theorem fusedMap0127_checked : acceptsGraphIso
    (fused (graph core0127) (root 4) 0 0) DegreeOneSmallSpectrum009.graph fusedMap0127=true := by decide +kernel
theorem certified0127 : Certified (graph core0127) (root 4) 0 0 :=
  of_native_maps core0127 DegreeOneSmallSpectrum014.graph DegreeOneSmallSpectrum009.graph
    sourceMap0127 fusedMap0127 sourceMap0127_checked fusedMap0127_checked
    DegreeOneSmallComparisons.comparison0127
#print axioms sourceMap0127_checked
#print axioms fusedMap0127_checked
#print axioms certified0127
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
