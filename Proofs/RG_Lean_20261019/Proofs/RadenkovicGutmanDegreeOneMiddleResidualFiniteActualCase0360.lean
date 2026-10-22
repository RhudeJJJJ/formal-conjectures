/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0360 : Family 9 := level9.get ⟨252,by decide⟩
def sourceMap0360 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0360 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0360_checked : acceptsGraphIso
    (source (graph core0360) (root 9) 2 2) DegreeOneMiddleResidualSpectrum873.graph sourceMap0360=true := by decide +kernel
theorem fusedMap0360_checked : acceptsGraphIso
    (fused (graph core0360) (root 9) 2 2) DegreeTwoThreeSpectrum4060.graph fusedMap0360=true := by decide +kernel
theorem certified0360 : Certified (graph core0360) (root 9) 2 2 :=
  of_native_maps core0360 DegreeOneMiddleResidualSpectrum873.graph DegreeTwoThreeSpectrum4060.graph
    sourceMap0360 fusedMap0360 sourceMap0360_checked fusedMap0360_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0360
#print axioms sourceMap0360_checked
#print axioms fusedMap0360_checked
#print axioms certified0360
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
