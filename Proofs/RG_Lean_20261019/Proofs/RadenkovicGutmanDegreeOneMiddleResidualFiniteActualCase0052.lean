/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0052 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0052 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap0052 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0052_checked : acceptsGraphIso
    (source (graph core0052) (root 5) 2 4) DegreeOneMiddleResidualSpectrum060.graph sourceMap0052=true := by decide +kernel
theorem fusedMap0052_checked : acceptsGraphIso
    (fused (graph core0052) (root 5) 2 4) DegreeTwoThreeSpectrum1709.graph fusedMap0052=true := by decide +kernel
theorem certified0052 : Certified (graph core0052) (root 5) 2 4 :=
  of_native_maps core0052 DegreeOneMiddleResidualSpectrum060.graph DegreeTwoThreeSpectrum1709.graph
    sourceMap0052 fusedMap0052 sourceMap0052_checked fusedMap0052_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0052
#print axioms sourceMap0052_checked
#print axioms fusedMap0052_checked
#print axioms certified0052
def sourceMap0052swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,0,10,11,12,13,7,8,9] (sourceLabel 5 4 2 v)
def fusedMap0052swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0052swap_checked : acceptsGraphIso
    (source (graph core0052) (root 5) 4 2) DegreeOneMiddleResidualSpectrum060.graph sourceMap0052swap=true := by decide +kernel
theorem fusedMap0052swap_checked : acceptsGraphIso
    (fused (graph core0052) (root 5) 4 2) DegreeTwoThreeSpectrum1709.graph fusedMap0052swap=true := by decide +kernel
theorem certified0052swap : Certified (graph core0052) (root 5) 4 2 :=
  of_native_maps core0052 DegreeOneMiddleResidualSpectrum060.graph DegreeTwoThreeSpectrum1709.graph
    sourceMap0052swap fusedMap0052swap sourceMap0052swap_checked fusedMap0052swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0052
#print axioms sourceMap0052swap_checked
#print axioms fusedMap0052swap_checked
#print axioms certified0052swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
