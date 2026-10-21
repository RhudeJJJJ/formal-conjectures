/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0294 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0294 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![2,1,0,5,6,7,8,3,4] (sourceLabel 6 0 0 v)
def fusedMap0294 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,5,0,1,2,3,4,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0294_checked : acceptsGraphIso
    (source (graph core0294) (root 6) 0 0) DegreeOneSmallSpectrum052.graph sourceMap0294=true := by decide +kernel
theorem fusedMap0294_checked : acceptsGraphIso
    (fused (graph core0294) (root 6) 0 0) DegreeOneSmallSpectrum036.graph fusedMap0294=true := by decide +kernel
theorem certified0294 : Certified (graph core0294) (root 6) 0 0 :=
  of_native_maps core0294 DegreeOneSmallSpectrum052.graph DegreeOneSmallSpectrum036.graph
    sourceMap0294 fusedMap0294 sourceMap0294_checked fusedMap0294_checked
    DegreeOneSmallComparisons.comparison0294
#print axioms sourceMap0294_checked
#print axioms fusedMap0294_checked
#print axioms certified0294
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
