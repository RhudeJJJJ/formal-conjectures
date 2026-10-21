/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0483 : Family 7 := level7.get ⟨7,by decide⟩
def sourceMap0483 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (sourceLabel 7 0 0 v)
def fusedMap0483 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0483_checked : acceptsGraphIso
    (source (graph core0483) (root 7) 0 0) DegreeOneSmallSpectrum103.graph sourceMap0483=true := by decide +kernel
theorem fusedMap0483_checked : acceptsGraphIso
    (fused (graph core0483) (root 7) 0 0) DegreeOneSmallSpectrum074.graph fusedMap0483=true := by decide +kernel
theorem certified0483 : Certified (graph core0483) (root 7) 0 0 :=
  of_native_maps core0483 DegreeOneSmallSpectrum103.graph DegreeOneSmallSpectrum074.graph
    sourceMap0483 fusedMap0483 sourceMap0483_checked fusedMap0483_checked
    DegreeOneSmallComparisons.comparison0483
#print axioms sourceMap0483_checked
#print axioms fusedMap0483_checked
#print axioms certified0483
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
