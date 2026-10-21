/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0240 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0240 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap0240 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0240_checked : acceptsGraphIso
    (source (graph core0240) (root 5) 1 4) DegreeOneSmallSpectrum1319.graph sourceMap0240=true := by decide +kernel
theorem fusedMap0240_checked : acceptsGraphIso
    (fused (graph core0240) (root 5) 1 4) DegreeOneSmallSpectrum915.graph fusedMap0240=true := by decide +kernel
theorem certified0240 : Certified (graph core0240) (root 5) 1 4 :=
  of_native_maps core0240 DegreeOneSmallSpectrum1319.graph DegreeOneSmallSpectrum915.graph
    sourceMap0240 fusedMap0240 sourceMap0240_checked fusedMap0240_checked
    DegreeOneSmallComparisons.comparison0240
#print axioms sourceMap0240_checked
#print axioms fusedMap0240_checked
#print axioms certified0240
def sourceMap0240swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,12,7,8] (sourceLabel 5 4 1 v)
def fusedMap0240swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0240swap_checked : acceptsGraphIso
    (source (graph core0240) (root 5) 4 1) DegreeOneSmallSpectrum1319.graph sourceMap0240swap=true := by decide +kernel
theorem fusedMap0240swap_checked : acceptsGraphIso
    (fused (graph core0240) (root 5) 4 1) DegreeOneSmallSpectrum915.graph fusedMap0240swap=true := by decide +kernel
theorem certified0240swap : Certified (graph core0240) (root 5) 4 1 :=
  of_native_maps core0240 DegreeOneSmallSpectrum1319.graph DegreeOneSmallSpectrum915.graph
    sourceMap0240swap fusedMap0240swap sourceMap0240swap_checked fusedMap0240swap_checked
    DegreeOneSmallComparisons.comparison0240
#print axioms sourceMap0240swap_checked
#print axioms fusedMap0240swap_checked
#print axioms certified0240swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
