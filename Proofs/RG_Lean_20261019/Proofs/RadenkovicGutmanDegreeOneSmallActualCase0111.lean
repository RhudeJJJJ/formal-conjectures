/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0111 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0111 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![1,0,4,5,6,2,3] (sourceLabel 4 0 0 v)
def fusedMap0111 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![4,0,1,2,3,5,6] (fusedLabel 4 0 0 v)
theorem sourceMap0111_checked : acceptsGraphIso
    (source (graph core0111) (root 4) 0 0) DegreeOneSmallSpectrum013.graph sourceMap0111=true := by decide +kernel
theorem fusedMap0111_checked : acceptsGraphIso
    (fused (graph core0111) (root 4) 0 0) DegreeOneSmallSpectrum008.graph fusedMap0111=true := by decide +kernel
theorem certified0111 : Certified (graph core0111) (root 4) 0 0 :=
  of_native_maps core0111 DegreeOneSmallSpectrum013.graph DegreeOneSmallSpectrum008.graph
    sourceMap0111 fusedMap0111 sourceMap0111_checked fusedMap0111_checked
    DegreeOneSmallComparisons.comparison0111
#print axioms sourceMap0111_checked
#print axioms fusedMap0111_checked
#print axioms certified0111
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
