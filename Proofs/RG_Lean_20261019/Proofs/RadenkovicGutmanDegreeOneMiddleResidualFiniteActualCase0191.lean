/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0191 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0191 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0191 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0191_checked : acceptsGraphIso
    (source (graph core0191) (root 6) 2 4) DegreeOneMiddleResidualSpectrum300.graph sourceMap0191=true := by decide +kernel
theorem fusedMap0191_checked : acceptsGraphIso
    (fused (graph core0191) (root 6) 2 4) DegreeTwoThreeSpectrum2349.graph fusedMap0191=true := by decide +kernel
theorem certified0191 : Certified (graph core0191) (root 6) 2 4 :=
  of_native_maps core0191 DegreeOneMiddleResidualSpectrum300.graph DegreeTwoThreeSpectrum2349.graph
    sourceMap0191 fusedMap0191 sourceMap0191_checked fusedMap0191_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0191
#print axioms sourceMap0191_checked
#print axioms fusedMap0191_checked
#print axioms certified0191
def sourceMap0191swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,11,12,13,14,8,9,10] (sourceLabel 6 4 2 v)
def fusedMap0191swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0191swap_checked : acceptsGraphIso
    (source (graph core0191) (root 6) 4 2) DegreeOneMiddleResidualSpectrum300.graph sourceMap0191swap=true := by decide +kernel
theorem fusedMap0191swap_checked : acceptsGraphIso
    (fused (graph core0191) (root 6) 4 2) DegreeTwoThreeSpectrum2349.graph fusedMap0191swap=true := by decide +kernel
theorem certified0191swap : Certified (graph core0191) (root 6) 4 2 :=
  of_native_maps core0191 DegreeOneMiddleResidualSpectrum300.graph DegreeTwoThreeSpectrum2349.graph
    sourceMap0191swap fusedMap0191swap sourceMap0191swap_checked fusedMap0191swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0191
#print axioms sourceMap0191swap_checked
#print axioms fusedMap0191swap_checked
#print axioms certified0191swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
