/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0926 : Family 10 := level10.get ⟨730,by decide⟩
def sourceMap0926 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0926 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0926_checked : acceptsGraphIso
    (source (graph core0926) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2197.graph sourceMap0926=true := by decide +kernel
theorem fusedMap0926_checked : acceptsGraphIso
    (fused (graph core0926) (root 10) 2 2) DegreeTwoThreeSpectrum5486.graph fusedMap0926=true := by decide +kernel
theorem certified0926 : Certified (graph core0926) (root 10) 2 2 :=
  of_native_maps core0926 DegreeOneMiddleResidualSpectrum2197.graph DegreeTwoThreeSpectrum5486.graph
    sourceMap0926 fusedMap0926 sourceMap0926_checked fusedMap0926_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0926
#print axioms sourceMap0926_checked
#print axioms fusedMap0926_checked
#print axioms certified0926
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
