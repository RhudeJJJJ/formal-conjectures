/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0628 : Family 10 := level10.get ⟨197,by decide⟩
def sourceMap0628 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0628 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0628_checked : acceptsGraphIso
    (source (graph core0628) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1568.graph sourceMap0628=true := by decide +kernel
theorem fusedMap0628_checked : acceptsGraphIso
    (fused (graph core0628) (root 10) 2 2) DegreeTwoThreeSpectrum5173.graph fusedMap0628=true := by decide +kernel
theorem certified0628 : Certified (graph core0628) (root 10) 2 2 :=
  of_native_maps core0628 DegreeOneMiddleResidualSpectrum1568.graph DegreeTwoThreeSpectrum5173.graph
    sourceMap0628 fusedMap0628 sourceMap0628_checked fusedMap0628_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0628
#print axioms sourceMap0628_checked
#print axioms fusedMap0628_checked
#print axioms certified0628
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
