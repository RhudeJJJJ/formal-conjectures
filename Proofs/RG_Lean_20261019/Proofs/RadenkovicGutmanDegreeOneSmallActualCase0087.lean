/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0087 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0087 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (sourceLabel 3 1 5 v)
def fusedMap0087 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 1 5 v)
theorem sourceMap0087_checked : acceptsGraphIso
    (source (graph core0087) (root 3) 1 5) DegreeOneSmallSpectrum434.graph sourceMap0087=true := by decide +kernel
theorem fusedMap0087_checked : acceptsGraphIso
    (fused (graph core0087) (root 3) 1 5) DegreeOneSmallSpectrum378.graph fusedMap0087=true := by decide +kernel
theorem certified0087 : Certified (graph core0087) (root 3) 1 5 :=
  of_native_maps core0087 DegreeOneSmallSpectrum434.graph DegreeOneSmallSpectrum378.graph
    sourceMap0087 fusedMap0087 sourceMap0087_checked fusedMap0087_checked
    DegreeOneSmallComparisons.comparison0087
#print axioms sourceMap0087_checked
#print axioms fusedMap0087_checked
#print axioms certified0087
def sourceMap0087swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,8,9,10,11,6,7] (sourceLabel 3 5 1 v)
def fusedMap0087swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 5 1 v)
theorem sourceMap0087swap_checked : acceptsGraphIso
    (source (graph core0087) (root 3) 5 1) DegreeOneSmallSpectrum434.graph sourceMap0087swap=true := by decide +kernel
theorem fusedMap0087swap_checked : acceptsGraphIso
    (fused (graph core0087) (root 3) 5 1) DegreeOneSmallSpectrum378.graph fusedMap0087swap=true := by decide +kernel
theorem certified0087swap : Certified (graph core0087) (root 3) 5 1 :=
  of_native_maps core0087 DegreeOneSmallSpectrum434.graph DegreeOneSmallSpectrum378.graph
    sourceMap0087swap fusedMap0087swap sourceMap0087swap_checked fusedMap0087swap_checked
    DegreeOneSmallComparisons.comparison0087
#print axioms sourceMap0087swap_checked
#print axioms fusedMap0087swap_checked
#print axioms certified0087swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
