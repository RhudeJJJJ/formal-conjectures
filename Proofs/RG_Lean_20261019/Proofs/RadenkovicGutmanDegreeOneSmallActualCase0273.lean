/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0273 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0273 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 6 1 2 v)
def fusedMap0273 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 6 1 2 v)
theorem sourceMap0273_checked : acceptsGraphIso
    (source (graph core0273) (root 6) 1 2) DegreeOneSmallSpectrum387.graph sourceMap0273=true := by decide +kernel
theorem fusedMap0273_checked : acceptsGraphIso
    (fused (graph core0273) (root 6) 1 2) DegreeOneSmallSpectrum369.graph fusedMap0273=true := by decide +kernel
theorem certified0273 : Certified (graph core0273) (root 6) 1 2 :=
  of_native_maps core0273 DegreeOneSmallSpectrum387.graph DegreeOneSmallSpectrum369.graph
    sourceMap0273 fusedMap0273 sourceMap0273_checked fusedMap0273_checked
    DegreeOneSmallComparisons.comparison0273
#print axioms sourceMap0273_checked
#print axioms fusedMap0273_checked
#print axioms certified0273
def sourceMap0273swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 6 2 1 v)
def fusedMap0273swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 6 2 1 v)
theorem sourceMap0273swap_checked : acceptsGraphIso
    (source (graph core0273) (root 6) 2 1) DegreeOneSmallSpectrum387.graph sourceMap0273swap=true := by decide +kernel
theorem fusedMap0273swap_checked : acceptsGraphIso
    (fused (graph core0273) (root 6) 2 1) DegreeOneSmallSpectrum369.graph fusedMap0273swap=true := by decide +kernel
theorem certified0273swap : Certified (graph core0273) (root 6) 2 1 :=
  of_native_maps core0273 DegreeOneSmallSpectrum387.graph DegreeOneSmallSpectrum369.graph
    sourceMap0273swap fusedMap0273swap sourceMap0273swap_checked fusedMap0273swap_checked
    DegreeOneSmallComparisons.comparison0273
#print axioms sourceMap0273swap_checked
#print axioms fusedMap0273swap_checked
#print axioms certified0273swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
