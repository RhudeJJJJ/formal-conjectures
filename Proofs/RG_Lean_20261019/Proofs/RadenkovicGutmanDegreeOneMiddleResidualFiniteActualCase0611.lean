/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0611 : Family 10 := level10.get ⟨166,by decide⟩
def sourceMap0611 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0611 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0611_checked : acceptsGraphIso
    (source (graph core0611) (root 10) 2 2) DegreeTwoThreeSpectrum6864.graph sourceMap0611=true := by decide +kernel
theorem fusedMap0611_checked : acceptsGraphIso
    (fused (graph core0611) (root 10) 2 2) DegreeTwoThreeSpectrum5108.graph fusedMap0611=true := by decide +kernel
theorem certified0611 : Certified (graph core0611) (root 10) 2 2 :=
  of_native_maps core0611 DegreeTwoThreeSpectrum6864.graph DegreeTwoThreeSpectrum5108.graph
    sourceMap0611 fusedMap0611 sourceMap0611_checked fusedMap0611_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0611
#print axioms sourceMap0611_checked
#print axioms fusedMap0611_checked
#print axioms certified0611
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
