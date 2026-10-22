/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0239 : Family 9 := level9.get ⟨51,by decide⟩
def sourceMap0239 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0239 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0239_checked : acceptsGraphIso
    (source (graph core0239) (root 9) 2 2) DegreeOneMiddleResidualSpectrum611.graph sourceMap0239=true := by decide +kernel
theorem fusedMap0239_checked : acceptsGraphIso
    (fused (graph core0239) (root 9) 2 2) DegreeTwoThreeSpectrum3931.graph fusedMap0239=true := by decide +kernel
theorem certified0239 : Certified (graph core0239) (root 9) 2 2 :=
  of_native_maps core0239 DegreeOneMiddleResidualSpectrum611.graph DegreeTwoThreeSpectrum3931.graph
    sourceMap0239 fusedMap0239 sourceMap0239_checked fusedMap0239_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0239
#print axioms sourceMap0239_checked
#print axioms fusedMap0239_checked
#print axioms certified0239
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
