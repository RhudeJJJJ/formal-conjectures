/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0235 : Family 9 := level9.get ⟨46,by decide⟩
def sourceMap0235 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0235 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0235_checked : acceptsGraphIso
    (source (graph core0235) (root 9) 2 2) DegreeOneMiddleResidualSpectrum586.graph sourceMap0235=true := by decide +kernel
theorem fusedMap0235_checked : acceptsGraphIso
    (fused (graph core0235) (root 9) 2 2) DegreeTwoThreeSpectrum3911.graph fusedMap0235=true := by decide +kernel
theorem certified0235 : Certified (graph core0235) (root 9) 2 2 :=
  of_native_maps core0235 DegreeOneMiddleResidualSpectrum586.graph DegreeTwoThreeSpectrum3911.graph
    sourceMap0235 fusedMap0235 sourceMap0235_checked fusedMap0235_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0235
#print axioms sourceMap0235_checked
#print axioms fusedMap0235_checked
#print axioms certified0235
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
