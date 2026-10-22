/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0375 : Family 9 := level9.get ⟨277,by decide⟩
def sourceMap0375 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0375 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0375_checked : acceptsGraphIso
    (source (graph core0375) (root 9) 2 2) DegreeOneMiddleResidualSpectrum895.graph sourceMap0375=true := by decide +kernel
theorem fusedMap0375_checked : acceptsGraphIso
    (fused (graph core0375) (root 9) 2 2) DegreeTwoThreeSpectrum4094.graph fusedMap0375=true := by decide +kernel
theorem certified0375 : Certified (graph core0375) (root 9) 2 2 :=
  of_native_maps core0375 DegreeOneMiddleResidualSpectrum895.graph DegreeTwoThreeSpectrum4094.graph
    sourceMap0375 fusedMap0375 sourceMap0375_checked fusedMap0375_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0375
#print axioms sourceMap0375_checked
#print axioms fusedMap0375_checked
#print axioms certified0375
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
