/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0388 : Family 9 := level9.get ⟨319,by decide⟩
def sourceMap0388 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0388 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0388_checked : acceptsGraphIso
    (source (graph core0388) (root 9) 2 2) DegreeOneMiddleResidualSpectrum739.graph sourceMap0388=true := by decide +kernel
theorem fusedMap0388_checked : acceptsGraphIso
    (fused (graph core0388) (root 9) 2 2) DegreeTwoThreeSpectrum4179.graph fusedMap0388=true := by decide +kernel
theorem certified0388 : Certified (graph core0388) (root 9) 2 2 :=
  of_native_maps core0388 DegreeOneMiddleResidualSpectrum739.graph DegreeTwoThreeSpectrum4179.graph
    sourceMap0388 fusedMap0388 sourceMap0388_checked fusedMap0388_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0388
#print axioms sourceMap0388_checked
#print axioms fusedMap0388_checked
#print axioms certified0388
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
