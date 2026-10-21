/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0451 : Family 7 := level7.get ⟨0,by decide⟩
def sourceMap0451 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (sourceLabel 7 1 1 v)
def fusedMap0451 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 7 1 1 v)
theorem sourceMap0451_checked : acceptsGraphIso
    (source (graph core0451) (root 7) 1 1) DegreeOneSmallSpectrum379.graph sourceMap0451=true := by decide +kernel
theorem fusedMap0451_checked : acceptsGraphIso
    (fused (graph core0451) (root 7) 1 1) DegreeOneSmallSpectrum369.graph fusedMap0451=true := by decide +kernel
theorem certified0451 : Certified (graph core0451) (root 7) 1 1 :=
  of_native_maps core0451 DegreeOneSmallSpectrum379.graph DegreeOneSmallSpectrum369.graph
    sourceMap0451 fusedMap0451 sourceMap0451_checked fusedMap0451_checked
    DegreeOneSmallComparisons.comparison0451
#print axioms sourceMap0451_checked
#print axioms fusedMap0451_checked
#print axioms certified0451
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
