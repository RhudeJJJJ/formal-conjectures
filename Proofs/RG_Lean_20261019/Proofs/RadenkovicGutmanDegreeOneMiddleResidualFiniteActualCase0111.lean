/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0111 : Family 8 := level8.get ⟨72,by decide⟩
def sourceMap0111 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0111 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0111_checked : acceptsGraphIso
    (source (graph core0111) (root 8) 2 2) DegreeTwoThreeSpectrum3631.graph sourceMap0111=true := by decide +kernel
theorem fusedMap0111_checked : acceptsGraphIso
    (fused (graph core0111) (root 8) 2 2) DegreeTwoThreeSpectrum2383.graph fusedMap0111=true := by decide +kernel
theorem certified0111 : Certified (graph core0111) (root 8) 2 2 :=
  of_native_maps core0111 DegreeTwoThreeSpectrum3631.graph DegreeTwoThreeSpectrum2383.graph
    sourceMap0111 fusedMap0111 sourceMap0111_checked fusedMap0111_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0111
#print axioms sourceMap0111_checked
#print axioms fusedMap0111_checked
#print axioms certified0111
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
