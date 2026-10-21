/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0974 : Family 8 := level8.get ⟨84,by decide⟩
def sourceMap0974 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0974 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0974_checked : acceptsGraphIso
    (source (graph core0974) (root 8) 1 1) DegreeOneSmallSpectrum1315.graph sourceMap0974=true := by decide +kernel
theorem fusedMap0974_checked : acceptsGraphIso
    (fused (graph core0974) (root 8) 1 1) DegreeOneSmallSpectrum968.graph fusedMap0974=true := by decide +kernel
theorem certified0974 : Certified (graph core0974) (root 8) 1 1 :=
  of_native_maps core0974 DegreeOneSmallSpectrum1315.graph DegreeOneSmallSpectrum968.graph
    sourceMap0974 fusedMap0974 sourceMap0974_checked fusedMap0974_checked
    DegreeOneSmallComparisons.comparison0974
#print axioms sourceMap0974_checked
#print axioms fusedMap0974_checked
#print axioms certified0974
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
