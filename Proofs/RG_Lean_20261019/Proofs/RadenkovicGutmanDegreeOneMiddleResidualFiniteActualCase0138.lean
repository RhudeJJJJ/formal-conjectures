/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0138 : Family 8 := level8.get ⟨122,by decide⟩
def sourceMap0138 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0138 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0138_checked : acceptsGraphIso
    (source (graph core0138) (root 8) 2 2) DegreeOneMiddleResidualSpectrum291.graph sourceMap0138=true := by decide +kernel
theorem fusedMap0138_checked : acceptsGraphIso
    (fused (graph core0138) (root 8) 2 2) DegreeTwoThreeSpectrum2572.graph fusedMap0138=true := by decide +kernel
theorem certified0138 : Certified (graph core0138) (root 8) 2 2 :=
  of_native_maps core0138 DegreeOneMiddleResidualSpectrum291.graph DegreeTwoThreeSpectrum2572.graph
    sourceMap0138 fusedMap0138 sourceMap0138_checked fusedMap0138_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0138
#print axioms sourceMap0138_checked
#print axioms fusedMap0138_checked
#print axioms certified0138
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
