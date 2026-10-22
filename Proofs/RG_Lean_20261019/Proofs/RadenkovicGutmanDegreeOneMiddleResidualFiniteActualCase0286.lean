/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0286 : Family 9 := level9.get ⟨118,by decide⟩
def sourceMap0286 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0286 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0286_checked : acceptsGraphIso
    (source (graph core0286) (root 9) 2 2) DegreeOneMiddleResidualSpectrum705.graph sourceMap0286=true := by decide +kernel
theorem fusedMap0286_checked : acceptsGraphIso
    (fused (graph core0286) (root 9) 2 2) DegreeTwoThreeSpectrum4136.graph fusedMap0286=true := by decide +kernel
theorem certified0286 : Certified (graph core0286) (root 9) 2 2 :=
  of_native_maps core0286 DegreeOneMiddleResidualSpectrum705.graph DegreeTwoThreeSpectrum4136.graph
    sourceMap0286 fusedMap0286 sourceMap0286_checked fusedMap0286_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0286
#print axioms sourceMap0286_checked
#print axioms fusedMap0286_checked
#print axioms certified0286
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
