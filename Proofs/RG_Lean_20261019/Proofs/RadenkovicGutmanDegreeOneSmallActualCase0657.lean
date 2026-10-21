/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0657 : Family 7 := level7.get ⟨52,by decide⟩
def sourceMap0657 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,4,5,6,2,3] (sourceLabel 7 0 0 v)
def fusedMap0657 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0657_checked : acceptsGraphIso
    (source (graph core0657) (root 7) 0 0) DegreeOneSmallSpectrum108.graph sourceMap0657=true := by decide +kernel
theorem fusedMap0657_checked : acceptsGraphIso
    (fused (graph core0657) (root 7) 0 0) DegreeOneSmallSpectrum148.graph fusedMap0657=true := by decide +kernel
theorem certified0657 : Certified (graph core0657) (root 7) 0 0 :=
  of_native_maps core0657 DegreeOneSmallSpectrum108.graph DegreeOneSmallSpectrum148.graph
    sourceMap0657 fusedMap0657 sourceMap0657_checked fusedMap0657_checked
    DegreeOneSmallComparisons.comparison0657
#print axioms sourceMap0657_checked
#print axioms fusedMap0657_checked
#print axioms certified0657
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
