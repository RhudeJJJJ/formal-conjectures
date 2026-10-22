/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0079 : Family 8 := level8.get ⟨23,by decide⟩
def sourceMap0079 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0079 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0079_checked : acceptsGraphIso
    (source (graph core0079) (root 8) 2 2) DegreeOneMiddleResidualSpectrum237.graph sourceMap0079=true := by decide +kernel
theorem fusedMap0079_checked : acceptsGraphIso
    (fused (graph core0079) (root 8) 2 2) DegreeTwoThreeSpectrum2402.graph fusedMap0079=true := by decide +kernel
theorem certified0079 : Certified (graph core0079) (root 8) 2 2 :=
  of_native_maps core0079 DegreeOneMiddleResidualSpectrum237.graph DegreeTwoThreeSpectrum2402.graph
    sourceMap0079 fusedMap0079 sourceMap0079_checked fusedMap0079_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0079
#print axioms sourceMap0079_checked
#print axioms fusedMap0079_checked
#print axioms certified0079
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
