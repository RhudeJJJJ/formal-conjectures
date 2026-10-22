/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0609 : Family 10 := level10.get ⟨164,by decide⟩
def sourceMap0609 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0609 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0609_checked : acceptsGraphIso
    (source (graph core0609) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1941.graph sourceMap0609=true := by decide +kernel
theorem fusedMap0609_checked : acceptsGraphIso
    (fused (graph core0609) (root 10) 2 2) DegreeTwoThreeSpectrum5106.graph fusedMap0609=true := by decide +kernel
theorem certified0609 : Certified (graph core0609) (root 10) 2 2 :=
  of_native_maps core0609 DegreeOneMiddleResidualSpectrum1941.graph DegreeTwoThreeSpectrum5106.graph
    sourceMap0609 fusedMap0609 sourceMap0609_checked fusedMap0609_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0609
#print axioms sourceMap0609_checked
#print axioms fusedMap0609_checked
#print axioms certified0609
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
