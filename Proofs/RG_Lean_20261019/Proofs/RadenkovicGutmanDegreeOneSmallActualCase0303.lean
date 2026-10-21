/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0303 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0303 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![2,1,0,6,7,8,5,3,4] (sourceLabel 6 0 0 v)
def fusedMap0303 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,4,2,3] (fusedLabel 6 0 0 v)
theorem sourceMap0303_checked : acceptsGraphIso
    (source (graph core0303) (root 6) 0 0) DegreeOneSmallSpectrum047.graph sourceMap0303=true := by decide +kernel
theorem fusedMap0303_checked : acceptsGraphIso
    (fused (graph core0303) (root 6) 0 0) DegreeOneSmallSpectrum036.graph fusedMap0303=true := by decide +kernel
theorem certified0303 : Certified (graph core0303) (root 6) 0 0 :=
  of_native_maps core0303 DegreeOneSmallSpectrum047.graph DegreeOneSmallSpectrum036.graph
    sourceMap0303 fusedMap0303 sourceMap0303_checked fusedMap0303_checked
    DegreeOneSmallComparisons.comparison0303
#print axioms sourceMap0303_checked
#print axioms fusedMap0303_checked
#print axioms certified0303
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
