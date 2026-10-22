/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0815 : Family 10 := level10.get ⟨517,by decide⟩
def sourceMap0815 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0815 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0815_checked : acceptsGraphIso
    (source (graph core0815) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1996.graph sourceMap0815=true := by decide +kernel
theorem fusedMap0815_checked : acceptsGraphIso
    (fused (graph core0815) (root 10) 2 2) DegreeTwoThreeSpectrum5160.graph fusedMap0815=true := by decide +kernel
theorem certified0815 : Certified (graph core0815) (root 10) 2 2 :=
  of_native_maps core0815 DegreeOneMiddleResidualSpectrum1996.graph DegreeTwoThreeSpectrum5160.graph
    sourceMap0815 fusedMap0815 sourceMap0815_checked fusedMap0815_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0815
#print axioms sourceMap0815_checked
#print axioms fusedMap0815_checked
#print axioms certified0815
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
