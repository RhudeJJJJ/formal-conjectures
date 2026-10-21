/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0510 : Family 7 := level7.get ⟨12,by decide⟩
def sourceMap0510 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0510 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0510_checked : acceptsGraphIso
    (source (graph core0510) (root 7) 0 3) DegreeOneSmallSpectrum914.graph sourceMap0510=true := by decide +kernel
theorem fusedMap0510_checked : acceptsGraphIso
    (fused (graph core0510) (root 7) 0 3) DegreeOneSmallSpectrum915.graph fusedMap0510=true := by decide +kernel
theorem certified0510 : Certified (graph core0510) (root 7) 0 3 :=
  of_native_maps core0510 DegreeOneSmallSpectrum914.graph DegreeOneSmallSpectrum915.graph
    sourceMap0510 fusedMap0510 sourceMap0510_checked fusedMap0510_checked
    DegreeOneSmallComparisons.comparison0510
#print axioms sourceMap0510_checked
#print axioms fusedMap0510_checked
#print axioms certified0510
def sourceMap0510swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0510swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0510swap_checked : acceptsGraphIso
    (source (graph core0510) (root 7) 3 0) DegreeOneSmallSpectrum914.graph sourceMap0510swap=true := by decide +kernel
theorem fusedMap0510swap_checked : acceptsGraphIso
    (fused (graph core0510) (root 7) 3 0) DegreeOneSmallSpectrum915.graph fusedMap0510swap=true := by decide +kernel
theorem certified0510swap : Certified (graph core0510) (root 7) 3 0 :=
  of_native_maps core0510 DegreeOneSmallSpectrum914.graph DegreeOneSmallSpectrum915.graph
    sourceMap0510swap fusedMap0510swap sourceMap0510swap_checked fusedMap0510swap_checked
    DegreeOneSmallComparisons.comparison0510
#print axioms sourceMap0510swap_checked
#print axioms fusedMap0510swap_checked
#print axioms certified0510swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
