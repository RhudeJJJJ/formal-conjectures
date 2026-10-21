/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0248 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0248 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap0248 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap0248_checked : acceptsGraphIso
    (source (graph core0248) (root 5) 0 5) DegreeOneSmallSpectrum917.graph sourceMap0248=true := by decide +kernel
theorem fusedMap0248_checked : acceptsGraphIso
    (fused (graph core0248) (root 5) 0 5) DegreeOneSmallSpectrum922.graph fusedMap0248=true := by decide +kernel
theorem certified0248 : Certified (graph core0248) (root 5) 0 5 :=
  of_native_maps core0248 DegreeOneSmallSpectrum917.graph DegreeOneSmallSpectrum922.graph
    sourceMap0248 fusedMap0248 sourceMap0248_checked fusedMap0248_checked
    DegreeOneSmallComparisons.comparison0248
#print axioms sourceMap0248_checked
#print axioms fusedMap0248_checked
#print axioms certified0248
def sourceMap0248swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap0248swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap0248swap_checked : acceptsGraphIso
    (source (graph core0248) (root 5) 5 0) DegreeOneSmallSpectrum917.graph sourceMap0248swap=true := by decide +kernel
theorem fusedMap0248swap_checked : acceptsGraphIso
    (fused (graph core0248) (root 5) 5 0) DegreeOneSmallSpectrum922.graph fusedMap0248swap=true := by decide +kernel
theorem certified0248swap : Certified (graph core0248) (root 5) 5 0 :=
  of_native_maps core0248 DegreeOneSmallSpectrum917.graph DegreeOneSmallSpectrum922.graph
    sourceMap0248swap fusedMap0248swap sourceMap0248swap_checked fusedMap0248swap_checked
    DegreeOneSmallComparisons.comparison0248
#print axioms sourceMap0248swap_checked
#print axioms fusedMap0248swap_checked
#print axioms certified0248swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
