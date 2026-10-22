/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0848 : Family 10 := level10.get ⟨572,by decide⟩
def sourceMap0848 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0848 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0848_checked : acceptsGraphIso
    (source (graph core0848) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2062.graph sourceMap0848=true := by decide +kernel
theorem fusedMap0848_checked : acceptsGraphIso
    (fused (graph core0848) (root 10) 2 2) DegreeTwoThreeSpectrum5238.graph fusedMap0848=true := by decide +kernel
theorem certified0848 : Certified (graph core0848) (root 10) 2 2 :=
  of_native_maps core0848 DegreeOneMiddleResidualSpectrum2062.graph DegreeTwoThreeSpectrum5238.graph
    sourceMap0848 fusedMap0848 sourceMap0848_checked fusedMap0848_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0848
#print axioms sourceMap0848_checked
#print axioms fusedMap0848_checked
#print axioms certified0848
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
