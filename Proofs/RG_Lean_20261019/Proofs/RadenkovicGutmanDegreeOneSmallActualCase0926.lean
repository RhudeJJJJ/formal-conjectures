/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0926 : Family 8 := level8.get ⟨63,by decide⟩
def sourceMap0926 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0926 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0926_checked : acceptsGraphIso
    (source (graph core0926) (root 8) 1 1) DegreeOneSmallSpectrum1326.graph sourceMap0926=true := by decide +kernel
theorem fusedMap0926_checked : acceptsGraphIso
    (fused (graph core0926) (root 8) 1 1) DegreeOneSmallSpectrum925.graph fusedMap0926=true := by decide +kernel
theorem certified0926 : Certified (graph core0926) (root 8) 1 1 :=
  of_native_maps core0926 DegreeOneSmallSpectrum1326.graph DegreeOneSmallSpectrum925.graph
    sourceMap0926 fusedMap0926 sourceMap0926_checked fusedMap0926_checked
    DegreeOneSmallComparisons.comparison0926
#print axioms sourceMap0926_checked
#print axioms fusedMap0926_checked
#print axioms certified0926
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
