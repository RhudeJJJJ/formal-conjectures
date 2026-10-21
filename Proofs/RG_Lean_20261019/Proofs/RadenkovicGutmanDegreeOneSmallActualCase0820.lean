/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0820 : Family 8 := level8.get ⟨25,by decide⟩
def sourceMap0820 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0820 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0820_checked : acceptsGraphIso
    (source (graph core0820) (root 8) 0 1) DegreeOneSmallSpectrum559.graph sourceMap0820=true := by decide +kernel
theorem fusedMap0820_checked : acceptsGraphIso
    (fused (graph core0820) (root 8) 0 1) DegreeOneSmallSpectrum393.graph fusedMap0820=true := by decide +kernel
theorem certified0820 : Certified (graph core0820) (root 8) 0 1 :=
  of_native_maps core0820 DegreeOneSmallSpectrum559.graph DegreeOneSmallSpectrum393.graph
    sourceMap0820 fusedMap0820 sourceMap0820_checked fusedMap0820_checked
    DegreeOneSmallComparisons.comparison0820
#print axioms sourceMap0820_checked
#print axioms fusedMap0820_checked
#print axioms certified0820
def sourceMap0820swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0820swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0820swap_checked : acceptsGraphIso
    (source (graph core0820) (root 8) 1 0) DegreeOneSmallSpectrum559.graph sourceMap0820swap=true := by decide +kernel
theorem fusedMap0820swap_checked : acceptsGraphIso
    (fused (graph core0820) (root 8) 1 0) DegreeOneSmallSpectrum393.graph fusedMap0820swap=true := by decide +kernel
theorem certified0820swap : Certified (graph core0820) (root 8) 1 0 :=
  of_native_maps core0820 DegreeOneSmallSpectrum559.graph DegreeOneSmallSpectrum393.graph
    sourceMap0820swap fusedMap0820swap sourceMap0820swap_checked fusedMap0820swap_checked
    DegreeOneSmallComparisons.comparison0820
#print axioms sourceMap0820swap_checked
#print axioms fusedMap0820swap_checked
#print axioms certified0820swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
