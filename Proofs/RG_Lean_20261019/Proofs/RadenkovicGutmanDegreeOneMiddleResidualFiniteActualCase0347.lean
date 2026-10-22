/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0347 : Family 9 := level9.get ⟨226,by decide⟩
def sourceMap0347 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0347 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0347_checked : acceptsGraphIso
    (source (graph core0347) (root 9) 2 2) DegreeOneMiddleResidualSpectrum853.graph sourceMap0347=true := by decide +kernel
theorem fusedMap0347_checked : acceptsGraphIso
    (fused (graph core0347) (root 9) 2 2) DegreeTwoThreeSpectrum4018.graph fusedMap0347=true := by decide +kernel
theorem certified0347 : Certified (graph core0347) (root 9) 2 2 :=
  of_native_maps core0347 DegreeOneMiddleResidualSpectrum853.graph DegreeTwoThreeSpectrum4018.graph
    sourceMap0347 fusedMap0347 sourceMap0347_checked fusedMap0347_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0347
#print axioms sourceMap0347_checked
#print axioms fusedMap0347_checked
#print axioms certified0347
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
