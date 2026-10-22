/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0486 : Family 10 := level10.get ⟨2,by decide⟩
def sourceMap0486 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0486 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0486_checked : acceptsGraphIso
    (source (graph core0486) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1362.graph sourceMap0486=true := by decide +kernel
theorem fusedMap0486_checked : acceptsGraphIso
    (fused (graph core0486) (root 10) 2 2) DegreeTwoThreeSpectrum4960.graph fusedMap0486=true := by decide +kernel
theorem certified0486 : Certified (graph core0486) (root 10) 2 2 :=
  of_native_maps core0486 DegreeOneMiddleResidualSpectrum1362.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap0486 fusedMap0486 sourceMap0486_checked fusedMap0486_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0486
#print axioms sourceMap0486_checked
#print axioms fusedMap0486_checked
#print axioms certified0486
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
