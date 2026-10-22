/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0127 : Family 8 := level8.get ⟨103,by decide⟩
def sourceMap0127 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0127 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0127_checked : acceptsGraphIso
    (source (graph core0127) (root 8) 2 2) DegreeOneMiddleResidualSpectrum272.graph sourceMap0127=true := by decide +kernel
theorem fusedMap0127_checked : acceptsGraphIso
    (fused (graph core0127) (root 8) 2 2) DegreeTwoThreeSpectrum2477.graph fusedMap0127=true := by decide +kernel
theorem certified0127 : Certified (graph core0127) (root 8) 2 2 :=
  of_native_maps core0127 DegreeOneMiddleResidualSpectrum272.graph DegreeTwoThreeSpectrum2477.graph
    sourceMap0127 fusedMap0127 sourceMap0127_checked fusedMap0127_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0127
#print axioms sourceMap0127_checked
#print axioms fusedMap0127_checked
#print axioms certified0127
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
