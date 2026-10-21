/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0785 : Family 8 := level8.get ⟨14,by decide⟩
def sourceMap0785 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0785 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0785_checked : acceptsGraphIso
    (source (graph core0785) (root 8) 0 2) DegreeOneSmallSpectrum913.graph sourceMap0785=true := by decide +kernel
theorem fusedMap0785_checked : acceptsGraphIso
    (fused (graph core0785) (root 8) 0 2) DegreeOneSmallSpectrum915.graph fusedMap0785=true := by decide +kernel
theorem certified0785 : Certified (graph core0785) (root 8) 0 2 :=
  of_native_maps core0785 DegreeOneSmallSpectrum913.graph DegreeOneSmallSpectrum915.graph
    sourceMap0785 fusedMap0785 sourceMap0785_checked fusedMap0785_checked
    DegreeOneSmallComparisons.comparison0785
#print axioms sourceMap0785_checked
#print axioms fusedMap0785_checked
#print axioms certified0785
def sourceMap0785swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0785swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0785swap_checked : acceptsGraphIso
    (source (graph core0785) (root 8) 2 0) DegreeOneSmallSpectrum913.graph sourceMap0785swap=true := by decide +kernel
theorem fusedMap0785swap_checked : acceptsGraphIso
    (fused (graph core0785) (root 8) 2 0) DegreeOneSmallSpectrum915.graph fusedMap0785swap=true := by decide +kernel
theorem certified0785swap : Certified (graph core0785) (root 8) 2 0 :=
  of_native_maps core0785 DegreeOneSmallSpectrum913.graph DegreeOneSmallSpectrum915.graph
    sourceMap0785swap fusedMap0785swap sourceMap0785swap_checked fusedMap0785swap_checked
    DegreeOneSmallComparisons.comparison0785
#print axioms sourceMap0785swap_checked
#print axioms fusedMap0785swap_checked
#print axioms certified0785swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
