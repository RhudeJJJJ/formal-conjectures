/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0122 : Family 8 := level8.get ⟨96,by decide⟩
def sourceMap0122 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0122 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0122_checked : acceptsGraphIso
    (source (graph core0122) (root 8) 2 2) DegreeOneMiddleResidualSpectrum263.graph sourceMap0122=true := by decide +kernel
theorem fusedMap0122_checked : acceptsGraphIso
    (fused (graph core0122) (root 8) 2 2) DegreeTwoThreeSpectrum2444.graph fusedMap0122=true := by decide +kernel
theorem certified0122 : Certified (graph core0122) (root 8) 2 2 :=
  of_native_maps core0122 DegreeOneMiddleResidualSpectrum263.graph DegreeTwoThreeSpectrum2444.graph
    sourceMap0122 fusedMap0122 sourceMap0122_checked fusedMap0122_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0122
#print axioms sourceMap0122_checked
#print axioms fusedMap0122_checked
#print axioms certified0122
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
