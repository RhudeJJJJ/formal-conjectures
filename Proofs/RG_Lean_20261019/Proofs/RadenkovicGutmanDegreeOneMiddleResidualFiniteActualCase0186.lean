/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0186 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0186 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0186 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0186_checked : acceptsGraphIso
    (source (graph core0186) (root 6) 2 4) DegreeTwoThreeSpectrum2879.graph sourceMap0186=true := by decide +kernel
theorem fusedMap0186_checked : acceptsGraphIso
    (fused (graph core0186) (root 6) 2 4) DegreeTwoThreeSpectrum2393.graph fusedMap0186=true := by decide +kernel
theorem certified0186 : Certified (graph core0186) (root 6) 2 4 :=
  of_native_maps core0186 DegreeTwoThreeSpectrum2879.graph DegreeTwoThreeSpectrum2393.graph
    sourceMap0186 fusedMap0186 sourceMap0186_checked fusedMap0186_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0186
#print axioms sourceMap0186_checked
#print axioms fusedMap0186_checked
#print axioms certified0186
def sourceMap0186swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap0186swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0186swap_checked : acceptsGraphIso
    (source (graph core0186) (root 6) 4 2) DegreeTwoThreeSpectrum2879.graph sourceMap0186swap=true := by decide +kernel
theorem fusedMap0186swap_checked : acceptsGraphIso
    (fused (graph core0186) (root 6) 4 2) DegreeTwoThreeSpectrum2393.graph fusedMap0186swap=true := by decide +kernel
theorem certified0186swap : Certified (graph core0186) (root 6) 4 2 :=
  of_native_maps core0186 DegreeTwoThreeSpectrum2879.graph DegreeTwoThreeSpectrum2393.graph
    sourceMap0186swap fusedMap0186swap sourceMap0186swap_checked fusedMap0186swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0186
#print axioms sourceMap0186swap_checked
#print axioms fusedMap0186swap_checked
#print axioms certified0186swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
