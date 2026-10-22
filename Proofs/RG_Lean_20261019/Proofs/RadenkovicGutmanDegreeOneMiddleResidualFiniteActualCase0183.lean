/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0183 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0183 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0183 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0183_checked : acceptsGraphIso
    (source (graph core0183) (root 6) 2 4) DegreeOneMiddleResidualSpectrum222.graph sourceMap0183=true := by decide +kernel
theorem fusedMap0183_checked : acceptsGraphIso
    (fused (graph core0183) (root 6) 2 4) DegreeTwoThreeSpectrum2359.graph fusedMap0183=true := by decide +kernel
theorem certified0183 : Certified (graph core0183) (root 6) 2 4 :=
  of_native_maps core0183 DegreeOneMiddleResidualSpectrum222.graph DegreeTwoThreeSpectrum2359.graph
    sourceMap0183 fusedMap0183 sourceMap0183_checked fusedMap0183_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0183
#print axioms sourceMap0183_checked
#print axioms fusedMap0183_checked
#print axioms certified0183
def sourceMap0183swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap0183swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0183swap_checked : acceptsGraphIso
    (source (graph core0183) (root 6) 4 2) DegreeOneMiddleResidualSpectrum222.graph sourceMap0183swap=true := by decide +kernel
theorem fusedMap0183swap_checked : acceptsGraphIso
    (fused (graph core0183) (root 6) 4 2) DegreeTwoThreeSpectrum2359.graph fusedMap0183swap=true := by decide +kernel
theorem certified0183swap : Certified (graph core0183) (root 6) 4 2 :=
  of_native_maps core0183 DegreeOneMiddleResidualSpectrum222.graph DegreeTwoThreeSpectrum2359.graph
    sourceMap0183swap fusedMap0183swap sourceMap0183swap_checked fusedMap0183swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0183
#print axioms sourceMap0183swap_checked
#print axioms fusedMap0183swap_checked
#print axioms certified0183swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
