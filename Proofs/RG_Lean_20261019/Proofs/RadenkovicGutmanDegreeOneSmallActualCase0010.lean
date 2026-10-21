/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0010 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0010 : (Vertices 1 ⊕ Fin 2 ⊕ Fin 2) → Fin 6 :=
  fun v => ![0,5,1,2,3,4] (sourceLabel 1 1 1 v)
def fusedMap0010 : (Vertices 1 ⊕ Fin 4) → Fin 6 :=
  fun v => ![1,2,0,3,4,5] (fusedLabel 1 1 1 v)
theorem sourceMap0010_checked : acceptsGraphIso
    (source (graph core0010) (root 1) 1 1) DegreeOneSmallSpectrum007.graph sourceMap0010=true := by decide +kernel
theorem fusedMap0010_checked : acceptsGraphIso
    (fused (graph core0010) (root 1) 1 1) DegreeOneSmallSpectrum004.graph fusedMap0010=true := by decide +kernel
theorem certified0010 : Certified (graph core0010) (root 1) 1 1 :=
  of_native_maps core0010 DegreeOneSmallSpectrum007.graph DegreeOneSmallSpectrum004.graph
    sourceMap0010 fusedMap0010 sourceMap0010_checked fusedMap0010_checked
    DegreeOneSmallComparisons.comparison0010
#print axioms sourceMap0010_checked
#print axioms fusedMap0010_checked
#print axioms certified0010
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
