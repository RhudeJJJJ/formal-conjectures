/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0000 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0000 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 1) → Fin 4 :=
  fun v => ![0,1,2,3] (sourceLabel 1 0 0 v)
def fusedMap0000 : (Vertices 1 ⊕ Fin 2) → Fin 4 :=
  fun v => ![0,1,2,3] (fusedLabel 1 0 0 v)
theorem sourceMap0000_checked : acceptsGraphIso
    (source (graph core0000) (root 1) 0 0) DegreeOneSmallSpectrum001.graph sourceMap0000=true := by decide +kernel
theorem fusedMap0000_checked : acceptsGraphIso
    (fused (graph core0000) (root 1) 0 0) DegreeOneSmallSpectrum000.graph fusedMap0000=true := by decide +kernel
theorem certified0000 : Certified (graph core0000) (root 1) 0 0 :=
  of_native_maps core0000 DegreeOneSmallSpectrum001.graph DegreeOneSmallSpectrum000.graph
    sourceMap0000 fusedMap0000 sourceMap0000_checked fusedMap0000_checked
    DegreeOneSmallComparisons.comparison0000
#print axioms sourceMap0000_checked
#print axioms fusedMap0000_checked
#print axioms certified0000
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
