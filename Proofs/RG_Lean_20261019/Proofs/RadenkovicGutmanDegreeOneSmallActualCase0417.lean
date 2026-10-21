/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0417 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0417 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0417 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0417_checked : acceptsGraphIso
    (source (graph core0417) (root 6) 1 2) DegreeOneSmallSpectrum727.graph sourceMap0417=true := by decide +kernel
theorem fusedMap0417_checked : acceptsGraphIso
    (fused (graph core0417) (root 6) 1 2) DegreeOneSmallSpectrum440.graph fusedMap0417=true := by decide +kernel
theorem certified0417 : Certified (graph core0417) (root 6) 1 2 :=
  of_native_maps core0417 DegreeOneSmallSpectrum727.graph DegreeOneSmallSpectrum440.graph
    sourceMap0417 fusedMap0417 sourceMap0417_checked fusedMap0417_checked
    DegreeOneSmallComparisons.comparison0417
#print axioms sourceMap0417_checked
#print axioms fusedMap0417_checked
#print axioms certified0417
def sourceMap0417swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0417swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0417swap_checked : acceptsGraphIso
    (source (graph core0417) (root 6) 2 1) DegreeOneSmallSpectrum727.graph sourceMap0417swap=true := by decide +kernel
theorem fusedMap0417swap_checked : acceptsGraphIso
    (fused (graph core0417) (root 6) 2 1) DegreeOneSmallSpectrum440.graph fusedMap0417swap=true := by decide +kernel
theorem certified0417swap : Certified (graph core0417) (root 6) 2 1 :=
  of_native_maps core0417 DegreeOneSmallSpectrum727.graph DegreeOneSmallSpectrum440.graph
    sourceMap0417swap fusedMap0417swap sourceMap0417swap_checked fusedMap0417swap_checked
    DegreeOneSmallComparisons.comparison0417
#print axioms sourceMap0417swap_checked
#print axioms fusedMap0417swap_checked
#print axioms certified0417swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
