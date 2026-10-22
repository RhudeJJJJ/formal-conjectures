/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0542 : Family 10 := level10.get ⟨70,by decide⟩
def sourceMap0542 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0542 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0542_checked : acceptsGraphIso
    (source (graph core0542) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1685.graph sourceMap0542=true := by decide +kernel
theorem fusedMap0542_checked : acceptsGraphIso
    (fused (graph core0542) (root 10) 2 2) DegreeTwoThreeSpectrum4984.graph fusedMap0542=true := by decide +kernel
theorem certified0542 : Certified (graph core0542) (root 10) 2 2 :=
  of_native_maps core0542 DegreeOneMiddleResidualSpectrum1685.graph DegreeTwoThreeSpectrum4984.graph
    sourceMap0542 fusedMap0542 sourceMap0542_checked fusedMap0542_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0542
#print axioms sourceMap0542_checked
#print axioms fusedMap0542_checked
#print axioms certified0542
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
