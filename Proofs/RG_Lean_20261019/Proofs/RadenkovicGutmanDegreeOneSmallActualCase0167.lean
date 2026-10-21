/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0167 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0167 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,5,6,1,2,3,4] (sourceLabel 5 1 3 v)
def fusedMap0167 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0167_checked : acceptsGraphIso
    (source (graph core0167) (root 5) 1 3) DegreeOneSmallSpectrum393.graph sourceMap0167=true := by decide +kernel
theorem fusedMap0167_checked : acceptsGraphIso
    (fused (graph core0167) (root 5) 1 3) DegreeOneSmallSpectrum369.graph fusedMap0167=true := by decide +kernel
theorem certified0167 : Certified (graph core0167) (root 5) 1 3 :=
  of_native_maps core0167 DegreeOneSmallSpectrum393.graph DegreeOneSmallSpectrum369.graph
    sourceMap0167 fusedMap0167 sourceMap0167_checked fusedMap0167_checked
    DegreeOneSmallComparisons.comparison0167
#print axioms sourceMap0167_checked
#print axioms fusedMap0167_checked
#print axioms certified0167
def sourceMap0167swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 3 1 v)
def fusedMap0167swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0167swap_checked : acceptsGraphIso
    (source (graph core0167) (root 5) 3 1) DegreeOneSmallSpectrum393.graph sourceMap0167swap=true := by decide +kernel
theorem fusedMap0167swap_checked : acceptsGraphIso
    (fused (graph core0167) (root 5) 3 1) DegreeOneSmallSpectrum369.graph fusedMap0167swap=true := by decide +kernel
theorem certified0167swap : Certified (graph core0167) (root 5) 3 1 :=
  of_native_maps core0167 DegreeOneSmallSpectrum393.graph DegreeOneSmallSpectrum369.graph
    sourceMap0167swap fusedMap0167swap sourceMap0167swap_checked fusedMap0167swap_checked
    DegreeOneSmallComparisons.comparison0167
#print axioms sourceMap0167swap_checked
#print axioms fusedMap0167swap_checked
#print axioms certified0167swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
