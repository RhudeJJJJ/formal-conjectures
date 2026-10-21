/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0150 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0150 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 4 1 1 v)
def fusedMap0150 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 1 1 v)
theorem sourceMap0150_checked : acceptsGraphIso
    (source (graph core0150) (root 4) 1 1) DegreeOneSmallSpectrum068.graph sourceMap0150=true := by decide +kernel
theorem fusedMap0150_checked : acceptsGraphIso
    (fused (graph core0150) (root 4) 1 1) DegreeOneSmallSpectrum042.graph fusedMap0150=true := by decide +kernel
theorem certified0150 : Certified (graph core0150) (root 4) 1 1 :=
  of_native_maps core0150 DegreeOneSmallSpectrum068.graph DegreeOneSmallSpectrum042.graph
    sourceMap0150 fusedMap0150 sourceMap0150_checked fusedMap0150_checked
    DegreeOneSmallComparisons.comparison0150
#print axioms sourceMap0150_checked
#print axioms fusedMap0150_checked
#print axioms certified0150
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
